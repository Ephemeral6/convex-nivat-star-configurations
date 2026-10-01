/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainGeom
import Nivat.External.Colle.ChainMax
import Nivat.External.Colle.ANormal
import Nivat.External.Colle.ChainRecursion
import Nivat.External.Colle.StepHypSeam
import Nivat.External.Colle.Claim36
import Nivat.External.Colle.GenClosureWeaken

/-!
# The assembly skeleton of `exists_chainData`, and what assembling it surfaces

Lane Aenvfix, 2026-09-19.  This file is upstream of `RegionSteps.lean` (its import closure
does not reach it) and does three things.

## 1. `ChainDataGeom.ofParts` — the smart constructor (§2)

`exists_chainData` (`RegionSteps.lean`) must produce a `ChainDataGeom`, a 46-obligation bundle
(`ChainData` 19 + `ChainDataWithShell` 4 + `ChainDataGeom` 23).  `ofParts` fixes the four data
fields that the paper fixes by formula,

    Ahat i       := hatOf A kk vl i                              -- `:488`
    shell i ε    := MaxEnv.shell (Ahat i) vJ1 nJ cJ ε            -- `:440`
    shellInf ε   := MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε       -- `:440`, so `shellInf_eq` is `rfl`
    fill i i₀ ε  := MaxEnv.genFill S gen (Ahat i ∪ shell i₀ ε)

and discharges every obligation that is mechanical once those choices are made.  **Its binder
list is the residual table** (CLAUDE.md hard rule 3: no hand-written status tables) — the
obligations that survive are exactly the hypotheses it takes.  Nothing here is `sorry`; a piece
that does not close stays a hypothesis.

The shell-block lemmas in §1 are ported from `tmp/tl_shell_wiring.lean` (team-lead,
2026-09-18, compiled there and never landed).  Seven of its eight are here; the eighth,
`shellSubStrip_of`, is **not** ported: it is stated at `kk ≡ 0` with the sweep direction equal
to `vl`, and the bundle sweeps along `vJ1`, not `vl` (`ChainDataWithShell.shellInf_eq`).  Its
general form (any `kk i`, sweep `v = m • vl`) is already in the build as
`ShellMink.ChainData.shell_subset_strip_of_nsmul`, and every transverse sweep is refuted there
by `ShellMink.not_shellSubStrip_of_transverse_sweep`; so `shellSubStrip` stays a hypothesis of
`ofParts` and is not re-proved here (PROTOCOL §20).

## 2. The seed and the single step (§3, §4)

* A future recursion needs a seed `B₀` that is `E(𝒮_φ)`-enveloped and on which some `T^{u₀} η`
  agrees with `x_per`.  Both are free: `𝒮_φ` is lattice convex, hence a lattice-convex region,
  hence `E(𝒮_φ)`-enveloped by `enveloped_refl`; and `x_per ∈ X_η` supplies `u₀` on any finite
  window (`Colle36.exists_shift_agreeing_on_finite`).  `exists_seed` packages this.
* `ChainMax.lean:77` says of `HasMaxEnvIn` that "nobody produces it yet".  That is out of
  date: `ChainRecursion.StepHyp` produces it at every `B` (`isMaxEnvIn_of_stepHyp`).  The
  fifth conjunct of `StepHyp`, which `chainA_spec` drops, is exactly `:484` maximality.

## 3. 🔴 The finding (§5): `ChainRecursion`'s construction choice `B (i+1) := A i` cannot reach `ChainDataGeom`

`ChainRecursion.lean` (2026-09-17, "construction choice accepted by team-lead") sets
`B (i+1) := A i` (`chainB_succ_eq_chainA`, `rfl`).  Then `subStrip` traps the whole chain in
`halfStrip (B 0) vl`, a band of bounded width transverse to `vl` when `B 0` is finite; but a
`ChainDataGeom` recedes along `v_J`, which is transverse to `vl` (`rec_vJ`, `dot_nJ_vJ`,
`dot_nJ_p`), so it cannot live in any such band.  Kernel statement:

    ChainDataGeom.false_of_chain_halfStrip :
      (∀ i, cg.B (i+1) ⊆ halfStrip (cg.A i) vl) → (cg.B 0).Finite → vl ≠ 0 → False

and, at the recursion itself, `not_chainDataGeom_of_chainRecursion`: no `ChainDataGeom` has
`B = chainB …` and `A = chainA …` over a finite seed.  `B 0` **is** finite on the route
`exists_chainData` serves (`hSfin_of_decompDataZ`, `SfinBound.lean`: every `E(𝒮_φ)`-enveloped set is
finite for `m ≥ 2`), and `vl ≠ 0` is `hvl_ne` at the hole.

This strictly strengthens the two earlier refutations.  `tmp/chaindata_kkzero_false.lean`
(`chainDataGeom_kk_zero_false`) needed `kk ≡ 0`, constant `u`, `p ≠ 0` and `p ∥ vl` on top of the
same `hchain`/`hB0`; `tmp/stephyp_landing_audit.lean` (`chainRecursion_forces_kk_nonzero`)
derived `hchain` and constant `u` from the recursion but still needed `kk ≡ 0`.  Here **`kk`,
`u`, `p`, the shell and the fill do not enter at all**.  Of the three escape valves listed in
`blueprint/LEAF-A.md` (`kk ≢ 0`, backward-growing `B`, non-constant `u`), two are closed by
this theorem and only one survives: **`B` must grow in all directions inside the half-plane**,
which is Collé's item (ii), `b3_colle2.txt:474` — `B_i ⊇ A_{i-1} ∪ ([-i+1, i-1]² ∩ ℋ(ℓ^(−)))` —
and is what makes `⋃ A_i = ℋ(ℓ^(−))` at `:495`.  Item (ii) is load-bearing, not bookkeeping.

Consequently the constructor `ofChain` drafted in `tmp/Aasm_ofChain.lean` (`ofParts` instantiated
on `chainB`/`chainA`, `check1.sh` EXIT=0) is **deliberately not landed**: its hypotheses are
jointly unsatisfiable whenever the seed is finite, so landing it would land a constructor with no
consistent instance.  `stepHyp_of_case2` (`StepHypSeam.lean`) is unaffected as a single-step
statement — it is `ChainRecursion.chainState`, the way the steps are chained, that has to be
replaced by one with item (ii).  That replacement is not attempted here.

**Reading, not kernel fact (PROTOCOL §15):** the corrected recursion will need `u` to vary with
`i` (item (iii): "for some `u_i`"), because agreement on a growing box cannot be had under a
fixed `u₀`; `ChainData.u : ℕ → ℤ × ℤ` already allows that, and `isMaxEnvIn_of_stepHyp` is stated
at a single `u₀` so it can be applied step by step with a different `u₀` each time.

`ChainDataGeom.false_of_ahat_band` below duplicates `ShellMink.ChainDataGeom.false_of_ahat_subset_band`
verbatim.  It cannot be imported: `ShellMink` imports `Step_PeriodsRays2`, which imports
`RegionSteps`, and this file must stay upstream of `RegionSteps` to be consumable there.  The
lemma only needs `ChainGeom` and `LatticeEdges`; moving the original upstream would let this copy
be deleted.
-/

set_option autoImplicit false

namespace Nivat.ChainAsm

open Nivat Nivat.LE2 Nivat.MaxEnv

/-! ## §1. The shell/fill block, ported from `tmp/tl_shell_wiring.lean`

Stated over an arbitrary chain `Ac` and sweep data `(v, n, c)`.  Each lemma names the
`ChainData` field it closes; `ofParts` consumes all seven. -/

section ShellBlock

variable {Ac : ℕ → Set (ℤ × ℤ)} {v n : ℤ × ℤ} {c : ℤ}

/-- **`ChainData.shellFinite`.** -/
theorem shellFinite_of (hfin : ∀ i, (Ac i).Finite) (hv : dot n v < 0) (i ε : ℕ) :
    (shell (Ac i) v n c ε).Finite :=
  shell_finite (hfin i) hv

/-- **`ChainData.subShell`.** -/
theorem subShell_of (hhp : ∀ i, Ac i ⊆ halfPlaneGE n c) (i ε : ℕ) :
    Ac i ⊆ shell (Ac i) v n c ε :=
  subset_shell ε (hhp i)

/-- **`ChainData.shellSubInf`.**  Free: the shell is monotone in its base set. -/
theorem shellSubInf_of (i ε : ℕ) :
    shell (Ac i) v n c ε ⊆ shell (⋃ j, Ac j) v n c ε :=
  shell_mono_set (Set.subset_iUnion Ac i)

/-- **`ChainData.shellProper`**, modulo an escape witness: some point of `Ac i` slides out of
`Ac i` along `v` while staying above level `c - ε`. -/
theorem shellProper_of {i ε : ℕ} {g : ℤ × ℤ} {t : ℕ} (hg : g ∈ Ac i)
    (hout : g + (t : ℤ) • v ∉ Ac i) (hlev : c - (ε : ℤ) ≤ dot n (g + (t : ℤ) • v)) :
    ¬ shell (Ac i) v n c ε ⊆ Ac i :=
  not_shell_subset hg hout hlev

/-- **`ChainData.fillZero`.**  `genFill … 0 = X` definitionally. -/
theorem fillZero_of (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ) (i i₀ ε : ℕ) :
    genFill S gen (Ac i ∪ shell (Ac i₀) v n c ε) 0 ⊆ Ac i ∪ shell (Ac i₀) v n c ε :=
  subset_rfl

/-- **`ChainData.fillStep`.**  By construction of `genFill`. -/
theorem fillStep_of (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ) (i i₀ ε m : ℕ) :
    ∀ z ∈ genFill S gen (Ac i ∪ shell (Ac i₀) v n c ε) (m + 1),
      z ∈ genFill S gen (Ac i ∪ shell (Ac i₀) v n c ε) m ∨
        ∃ t : ℤ × ℤ, z = gen + t ∧ ∀ b ∈ S.erase gen,
          b + t ∈ genFill S gen (Ac i ∪ shell (Ac i₀) v n c ε) m :=
  fun z hz => genFill_step S gen _ m z hz

/-- **`ChainData.shellInfZero`**, modulo `SweptClosed` on the limit set. -/
theorem shellInfZero_of (hhp : (⋃ j, Ac j) ⊆ halfPlaneGE n c)
    (hsw : SweptClosed (⋃ j, Ac j) v n c) :
    shell (⋃ j, Ac j) v n c 0 ⊆ ⋃ j, Ac j :=
  (shell_zero hhp hsw).subset

end ShellBlock

end Nivat.ChainAsm

/-! ## §2. The smart constructor -/

namespace Nivat.Colle35

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.ChainAsm

variable {α : Type*}

/-- **`ChainDataGeom` from its parts.**  The four data fields `Ahat`/`shell`/`shellInf`/`fill`
are fixed by the paper's formulas (module docstring); everything mechanical is discharged in the
body; **the hypotheses are the residual**.  Grouped:

* chain — `envShift envB maxA subBA subAB AhatMono` (`maxA` is `:484` maximality, which
  `ChainMax.lean` turns into `envA`/`subStrip`/`agreeA`/`maximalHat`);
* shell — `hsweep hfin hhp hswept ahat_nonempty shellSubStrip escape shellEnv fillCover`;
* face — `F : FaceBlock S nJ vJ` (eight face obligations, `ANormal.lean`), the binding
  `gen_eq : gen = F.a'` (below), and the two primitivity fields;
* region — `bottom rec_p dot_nJ_p rec_vJ`;
* `ℓ_ι` side — `cL ahat_halfPlane_L ahat_attained_L nfp_L`.

`escape`'s `ε` is pinned to `ℕ` explicitly: with `cJ - (ε : ℤ)` first in the binder it would
elaborate as `ℤ` and `shellProper`'s `0 < ε` would not match. -/
noncomputable def ChainDataGeom.ofParts
    (η xper : Config α) (vl p : ℤ × ℤ) (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ)
    (Env : Set (ℤ × ℤ) → Prop) (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ)
    (envShift : ∀ (v : ℤ × ℤ) (T : Set (ℤ × ℤ)), Env T → Env {z | z + v ∈ T})
    (envB : ∀ i, Env (B i))
    (maxA : ∀ i, IsMaxEnvIn Env (canonA η xper vl B u i) (A i))
    (subBA : ∀ i, B i ⊆ A i) (subAB : ∀ i, A i ⊆ B (i + 1))
    (AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j)
    (vJ1 nJ : ℤ × ℤ) (cJ : ℤ)
    (hsweep : dot nJ vJ1 < 0)
    (hfin : ∀ i, (hatOf A kk vl i).Finite)
    (hhp : ∀ i, hatOf A kk vl i ⊆ halfPlaneGE nJ cJ)
    (hswept : SweptClosed (⋃ i, hatOf A kk vl i) vJ1 nJ cJ)
    (ahat_nonempty : (⋃ i, hatOf A kk vl i).Nonempty)
    (shellSubStrip : ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → Env (shell (hatOf A kk vl i) vJ1 nJ cJ ε)) →
      ∀ i, i₀ ≤ i → shell (hatOf A kk vl i) vJ1 nJ cJ ε ⊆
        {z | z + (kk i : ℤ) • vl ∈ halfStrip (B i) vl})
    (escape : ∀ (i ε : ℕ), 0 < ε → ∃ g ∈ hatOf A kk vl i, ∃ t : ℕ,
      g + (t : ℤ) • vJ1 ∉ hatOf A kk vl i ∧ cJ - (ε : ℤ) ≤ dot nJ (g + (t : ℤ) • vJ1))
    (shellEnv : ∃ ε i₀, 0 < ε ∧ ∀ i, i₀ ≤ i → Env (shell (hatOf A kk vl i) vJ1 nJ cJ ε))
    (fillCover : ∀ i i₀ ε, i₀ ≤ i → shell (hatOf A kk vl i) vJ1 nJ cJ ε ⊆
      ⋃ n, genFill S gen (hatOf A kk vl i ∪ shell (hatOf A kk vl i₀) vJ1 nJ cJ ε) n)
    (vJ : ℤ × ℤ) (F : FaceBlock S nJ vJ)
    -- **The generating point is the `v_J`-forward end of the face** (2026-09-19, team-lead
    -- ruling on Amink's finding).  Kernel receipt (`tmp/aenvfix_fillCover_wit.lean`, and
    -- `FillCoverWitness.lean` once landed): on `ShellSweep`'s data at `(i, i₀, ε) = (2, 1, 1)`
    -- the `:518` `fillCover` instance holds for `gen = (1,0) = a'` (`lex'`, `v_J`-maximal) and
    -- fails for `gen = (0,0) = a`.  Reading, not kernel fact: `bottom` puts the new sites of
    -- `Â_∞^{(ε+1)}` on a `+v_J` half-line, so only the `+v_J` endpoint can generate them.
    -- Free at the producer given `IsGeneratingSet` (`FaceBlock.generatesAt_a'` below).
    (gen_eq : gen = F.a')
    (vJ_prim : Primitive vJ) (nJ_prim : Primitive nJ)
    (bottom : ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ reachSet (⋃ i, hatOf A kk vl i) vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k →
        z₀ + k • vJ + (b - F.a) ∈ reachSet (⋃ i, hatOf A kk vl i) vJ1) ∧
      (∀ z ∈ shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ (ε + 1),
        z ∈ shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ))
    (rec_p : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + p ∈ ⋃ i, hatOf A kk vl i)
    (dot_nJ_p : dot nJ p ≠ 0)
    (rec_vJ : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + vJ ∈ ⋃ i, hatOf A kk vl i)
    (cL : ℤ)
    (ahat_halfPlane_L : ∀ g ∈ ⋃ i, hatOf A kk vl i, cL ≤ dot (det p vJ • (-p.2, p.1)) g)
    (ahat_attained_L : ∃ g ∈ ⋃ i, hatOf A kk vl i, dot (det p vJ • (-p.2, p.1)) g = cL)
    (nfp_L : ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
      PeriodicOnWith xper {z | cL ≤ dot (det p vJ • (-p.2, p.1)) z} h ∧
      PeriodicOnWith xper {z | cL ≤ dot (det p vJ • (-p.2, p.1)) z} h') :
    ChainDataGeom η xper vl p S gen where
  Env := Env
  B := B
  A := A
  u := u
  kk := kk
  Ahat := hatOf A kk vl
  shell := fun i ε => shell (hatOf A kk vl i) vJ1 nJ cJ ε
  shellInf := fun ε => shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε
  fill := fun i i₀ ε => genFill S gen (hatOf A kk vl i ∪ shell (hatOf A kk vl i₀) vJ1 nJ cJ ε)
  envB := envB
  envA := envA_of_max maxA
  subBA := subBA
  subAB := subAB
  subStrip := subStrip_of_max maxA
  agreeA := agreeA_of_max maxA
  AhatEq := fun i => hatOf_eq i
  AhatMono := AhatMono
  maximalHat := maximalHat_of_max envShift maxA
  shellFinite := shellFinite_of hfin hsweep
  subShell := subShell_of hhp
  shellSubInf := shellSubInf_of
  shellInfZero := shellInfZero_of (Set.iUnion_subset hhp) hswept
  -- **`I₀`（第 162 轮）**：原文 `b3_colle2.txt:520` 的第二个常数，`:524`「if we consider
  -- `i ≥ max{i₀, I₀}`」。本入口的三条 shell 假设都还是第 159 轮的强形状（尾部 `i₀ ≤ i`），
  -- 所以取 `I₀ := 0`，在下面用 `le_max_left` 把 `max i₀ 0 ≤ i` 削回 `i₀ ≤ i`。
  I₀ := 0
  shellSubStrip := fun ε i₀ hε hEnv i hi =>
    shellSubStrip ε i₀ hε hEnv i (le_trans (le_max_left _ _) hi)
  -- 第 159 轮：`ChainData.shellProper` / `fillCover` 换成 `shellEnv` 守卫版
  -- （`Lemma35.lean:758` / `:777`）。`ofParts` 的 `escape` / `fillCover` **假设**保持原样
  -- （本入口不在链上，不值得改签名），只在这里把多出来的两条守卫收掉不用——守卫版更弱，
  -- 从强假设推弱字段永远可以。
  shellProper := fun ε _i₀ hε _hEnv i _hi => by
    obtain ⟨g, hg, t, hout, hlev⟩ := escape i ε hε
    exact shellProper_of hg hout hlev
  shellEnv := shellEnv
  fillZero := fillZero_of S gen
  -- `gen_eq` is consumed here so that the binding is part of the term, not a dead hypothesis.
  fillStep := by subst gen_eq; exact fillStep_of S F.a'
  -- Round 80 widened `ChainData.fillCover` (`Lemma35.lean:765`) from the single-generator
  -- filtration `⋃ n, fill i i₀ ε n` to the unrestricted `Colle37.GenClosure S (…)`.  The binder
  -- above is kept in the `genFill` shape — that is the shape every producer (`ChainExhaust`,
  -- `ChainExhaustInter`, the leaf-A assembly) already discharges — and weakened here by
  -- `genFill_subset_genClosure` (`GenClosureWeaken.lean:55`), whose two side conditions are
  -- exactly `F.a'_mem` and `latticeConvex_erase_of_lexExtreme … F.lex'` (`ShellGeom.lean:74`),
  -- both already spent by `fillStep` and `FaceBlock.generatesAt_a'` (`:298`).  One-way by
  -- design: `GenClosure ⊆ genFill` is false (`GenClosureWeaken.lean:37`).
  fillCover := by
    intro ε i₀ _hε _hEnv i hi z hz
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp
      (fillCover i i₀ ε (le_trans (le_max_left _ _) hi) hz)
    subst gen_eq
    exact GenClosureWeaken.genFill_subset_genClosure F.a'_mem
      (Nivat.Colle37Geom.latticeConvex_erase_of_lexExtreme F.latticeConvex_S F.lex') n z hn
  vJ1 := vJ1
  nJ := nJ
  cJ := cJ
  shellInf_eq := fun _ => rfl
  ahat_nonempty := ahat_nonempty
  ahat_halfPlane := fun g hg => Set.iUnion_subset hhp hg
  vJ := vJ
  a := F.a
  a' := F.a'
  r := F.r
  latticeConvex_S := F.latticeConvex_S
  a_mem := F.a_mem
  a'_mem := F.a'_mem
  lex := F.lex
  lex' := F.lex'
  edge := F.edge
  edge' := F.edge'
  dot_nJ_vJ := F.dot_nJ_vJ
  bottom := bottom
  rec_p := rec_p
  dot_nJ_p := dot_nJ_p
  vJ_ne := vJ_prim.ne_zero
  vJ_prim := vJ_prim
  rec_vJ := rec_vJ
  cL := cL
  ahat_halfPlane_L := ahat_halfPlane_L
  ahat_attained_L := ahat_attained_L
  nJ_prim := nJ_prim
  nfp_L := nfp_L

/-- **The `gen_eq` binder costs the producer nothing beyond `IsGeneratingSet`.**  `a'` is a
vertex of `S` — `lex'` makes `S.erase a'` lattice convex
(`Colle37Geom.latticeConvex_erase_of_lexExtreme`) — and a generating set generates at every
vertex (`IsGeneratingSet`, third conjunct).  `exists_preamble_pair` (`RegionSteps.lean`) exports
`IsGeneratingSet ξ d.Sphi`, so `exists_chainData`'s `GeneratesAt ξ d.Sphi genφ` conjunct is
this lemma at `genφ := F.a'`. -/
theorem FaceBlock.generatesAt_a' {ξ : Config α} {S : Finset (ℤ × ℤ)} {nJ vJ : ℤ × ℤ}
    (F : FaceBlock S nJ vJ) (hS : Nivat.Colle.IsGeneratingSet ξ S) :
    Nivat.Colle.GeneratesAt ξ S F.a' :=
  hS.2.2 F.a' F.a'_mem
    (Nivat.Colle37Geom.latticeConvex_erase_of_lexExtreme F.latticeConvex_S F.lex')

/-- `hatOf A kk vl i` is the shift of `A i` by `-(kk i) • vl`. -/
theorem hatOf_eq_shift (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (vl : ℤ × ℤ) (i : ℕ) :
    hatOf A kk vl i = shift (-(kk i : ℤ) • vl) (A i) := by
  ext z; simp [hatOf, shift]

/-- **Lattice-convexity of `Â_∞` from `ofParts`'s own binders plus the `Env` pin.**  This is
the content of `ColleReg.region_latticeConvex` (`RegionSteps.lean`) moved upstream of
`RegionSteps`, on the raw parts instead of a `ChainData`.  The pin `hEnv : Env = EnvOf ↑S` is
the one input `ofParts` does not carry — `Env` is a free parameter there and no binder
constrains it (reading, not kernel fact: `Env := fun _ => True` satisfies `envShift`, `envB`,
`shellEnv`) — and it is exactly the conjunct `exists_chainData` already exports
(`cg.toChainData.Env = EnvOf ↑S`).  Consumer: `ChainExhaust.ofPartsExhausts`, where it
replaces the `rec_vJ` binder via Amink's `rec_vJ_of_bottom` (`ItemII.lean`). -/
theorem latticeConvex_iUnion_hatOf (η xper : Config α) (vl : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    (Env : Set (ℤ × ℤ) → Prop) (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ)
    (hEnv : Env = EnvOf (↑S : Set (ℤ × ℤ)))
    (maxA : ∀ i, IsMaxEnvIn Env (canonA η xper vl B u i) (A i))
    (hfin : ∀ i, (hatOf A kk vl i).Finite)
    (AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j) :
    IsLatticeConvexRegion (⋃ i, hatOf A kk vl i) := by
  have henvA : ∀ i, Enveloped (↑S : Set (ℤ × ℤ)) (A i) := by
    intro i; have h := envA_of_max maxA i; rwa [hEnv] at h
  have hconv : ∀ i, IsLatticeConvexRegion (hatOf A kk vl i) := by
    intro i; rw [hatOf_eq_shift]
    exact isLatticeConvexRegion_shift _ (henvA i).1.1
  apply isLatticeConvexRegion_iUnion_of_mono_fixedEdges_finite (S := ↑S) AhatMono hconv hfin
  intro i
  rw [hatOf_eq_shift, E_shift]
  exact Enveloped.E_eq (finite_E_of_finite S.finite_toSet) (henvA i)

end Nivat.Colle35

namespace Nivat.ChainAsm

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35 Nivat.ColleReg4

/-! ## §3. The seed is free

Collé starts the chain from an `E(𝒮_φ)`-enveloped `B'` with `(0,0) ∈ B'`
(`b3_colle2.txt:462-464`).  `𝒮_φ` itself qualifies: it is lattice convex (`DecompDataZ.Sphi_conv`),
hence a lattice-convex region, hence `E(𝒮_φ)`-enveloped by reflexivity; and `x_per ∈ X_η` gives a
shift agreeing on any finite window.  What is *not* supplied here is the placement condition
"the support line of `B'` determined by `ℓ` coincides with `ℓ^(−)`" (`:464`), which is the same
placement obligation `nfp_L` carries (`ChainGeom.lean`, docstring of `nfp_L`). -/

/-- A finite lattice-convex set is a lattice-convex region: its own convex hull is the closed
convex witness, and lattice convexity is exactly `↑S = toReal ⁻¹' Conv S`. -/
theorem isLatticeConvexRegion_coe {S : Finset (ℤ × ℤ)} (hS : LatticeConvex S) :
    IsLatticeConvexRegion (↑S : Set (ℤ × ℤ)) :=
  ⟨Conv S, convex_convexHull ℝ _, (S.finite_toSet.image toReal).isClosed_convexHull ℝ,
    Set.ext fun z => hS.mem_iff z⟩

/-- A lattice-convex window is enveloped by its own edge set. -/
theorem envOf_coe_self {S : Finset (ℤ × ℤ)} (hS : LatticeConvex S) :
    EnvOf (↑S : Set (ℤ × ℤ)) (↑S : Set (ℤ × ℤ)) :=
  enveloped_refl _ (isLatticeConvexRegion_coe hS)

/-- **The seed of the chain recursion, from `x_per ∈ X_η` alone.**  This is the input triple
`(B0, hB0, hagree0)` of `ChainRecursion.chainState`, which that file leaves as "external data". -/
theorem exists_seed {ξ xper : Config ℤ} {S : Finset (ℤ × ℤ)} (hS : LatticeConvex S)
    (hxper : xper ∈ orbitClosure ξ) :
    ∃ (B0 : Set (ℤ × ℤ)) (u₀ : ℤ × ℤ), EnvOf (↑S : Set (ℤ × ℤ)) B0 ∧ B0.Finite ∧
      ∀ z ∈ B0, T u₀ ξ z = xper z := by
  obtain ⟨u₀, hu₀⟩ := Nivat.Colle36.exists_shift_agreeing_on_finite hxper S.finite_toSet
  exact ⟨↑S, u₀, envOf_coe_self hS, S.finite_toSet, hu₀⟩

/-! ## §4. `StepHyp` produces `:484` maximality

`ChainMax.HasMaxEnvIn` (`ChainMax.lean:78`) is documented as having no producer.  The fifth
conjunct of `ChainRecursion.StepHyp` — the one `chainA_spec` does not expose — is precisely
`IsMaxEnvIn` for the constraint set `canonA` at the constant sequence `u ≡ u₀`. -/

/-- **`:484` maximality of the `StepHyp` output.**  Stated at a single `B` and a single `u₀` so
that a recursion may apply it with a different `u₀` at each step. -/
theorem isMaxEnvIn_of_stepHyp {ξ xper : Config ℤ} {S : Finset (ℤ × ℤ)} {vl u₀ : ℤ × ℤ}
    (hstep : StepHyp ξ xper S vl u₀) {B : Set (ℤ × ℤ)} (hB : EnvOf (↑S : Set (ℤ × ℤ)) B)
    (hagree : ∀ z ∈ B, T u₀ ξ z = xper z) :
    IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ)))
      {w | w ∈ Colle35.halfStrip B vl ∧ ξ (w + u₀) = xper w}
      (Classical.choose (hstep B hB hagree)) := by
  obtain ⟨hEnv, hBA, hstrip, hagr, hmax⟩ := Classical.choose_spec (hstep B hB hagree)
  refine ⟨hEnv, fun w hw => ⟨hstrip hw, by simpa using hagr w hw⟩, ?_⟩
  intro Tset hT hAT hTC
  have hTstrip : Tset ⊆ Nivat.LE2.halfStrip B vl := fun w hw => (hTC hw).1
  have hTagr : ∀ z ∈ Tset, T u₀ ξ z = xper z := fun w hw => by simpa using (hTC hw).2
  have := hmax Tset hT (hBA.trans hAT) hTstrip hTagr hAT
  rw [this]

/-- The `∃` form that `ChainMax.lean` names. -/
theorem hasMaxEnvIn_of_stepHyp {ξ xper : Config ℤ} {S : Finset (ℤ × ℤ)} {vl u₀ : ℤ × ℤ}
    (hstep : StepHyp ξ xper S vl u₀) {B : Set (ℤ × ℤ)} (hB : EnvOf (↑S : Set (ℤ × ℤ)) B)
    (hagree : ∀ z ∈ B, T u₀ ξ z = xper z) :
    HasMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ)))
      {w | w ∈ Colle35.halfStrip B vl ∧ ξ (w + u₀) = xper w} :=
  ⟨_, isMaxEnvIn_of_stepHyp hstep hB hagree⟩

/-- **`ofParts.hfin` from finiteness of `A i`.**  `hatOf A kk vl i` is the preimage of `A i`
under a translation. -/
theorem hatOf_finite {A : ℕ → Set (ℤ × ℤ)} (kk : ℕ → ℕ) (vl : ℤ × ℤ)
    (hA : ∀ i, (A i).Finite) (i : ℕ) : (hatOf A kk vl i).Finite :=
  (hA i).preimage (Function.Injective.injOn (add_left_injective _))

/-! ## §5. 🔴 `B (i+1) := A i` cannot reach `ChainDataGeom`

See the module docstring.  The half-strip lemmas are those of `tmp/chaindata_kkzero_false.lean`
§1, unchanged. -/

theorem halfStrip_mono {B B' : Set (ℤ × ℤ)} {v : ℤ × ℤ} (h : B ⊆ B') :
    Colle35.halfStrip B v ⊆ Colle35.halfStrip B' v := by
  rintro z ⟨b, hb, t, rfl⟩
  exact ⟨b, h hb, t, rfl⟩

theorem halfStrip_halfStrip (B : Set (ℤ × ℤ)) (v : ℤ × ℤ) :
    Colle35.halfStrip (Colle35.halfStrip B v) v ⊆ Colle35.halfStrip B v := by
  rintro z ⟨_, ⟨b, hb, s, rfl⟩, t, rfl⟩
  refine ⟨b, hb, s + t, ?_⟩
  push_cast
  rw [add_smul]
  abel

/-- **A chain with `B (i+1) ⊆ halfStrip (A i) vl` lives in the half-strip of its seed.** -/
theorem chain_subset_halfStrip {B A : ℕ → Set (ℤ × ℤ)} {vl : ℤ × ℤ}
    (hstrip : ∀ i, A i ⊆ Colle35.halfStrip (B i) vl)
    (hchain : ∀ i, B (i + 1) ⊆ Colle35.halfStrip (A i) vl) :
    ∀ i, A i ⊆ Colle35.halfStrip (B 0) vl := by
  intro i
  induction i with
  | zero => exact hstrip 0
  | succ i ih =>
    exact (hstrip (i + 1)).trans ((halfStrip_mono (hchain i)).trans
      ((halfStrip_halfStrip _ _).trans ((halfStrip_mono ih).trans (halfStrip_halfStrip _ _))))

private theorem det_add_right (u x y : ℤ × ℤ) : det u (x + y) = det u x + det u y := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

/-- `det vl` is bounded on the half-strip of a finite set along `vl`: the half-strip is a band
of bounded width transverse to `vl`. -/
theorem det_bounded_on_halfStrip {B : Set (ℤ × ℤ)} (hB : B.Finite) (vl : ℤ × ℤ) :
    ∃ M : ℤ, ∀ z ∈ Colle35.halfStrip B vl, -M ≤ det vl z ∧ det vl z ≤ M := by
  obtain ⟨M, hM⟩ := (hB.image (fun b => |det vl b|)).bddAbove
  refine ⟨max M 0, ?_⟩
  rintro z ⟨b, hb, t, rfl⟩
  have hb' : |det vl b| ≤ M := hM ⟨b, hb, rfl⟩
  have hdet : det vl (b + (t : ℤ) • vl) = det vl b := by
    rw [det_add_right, Nivat.ColleReg.det_smul_right, det_self]; ring
  rw [hdet]
  exact abs_le.mp (hb'.trans (le_max_left _ _))

/-- **No `ChainDataGeom` has `Â_∞` inside a band.**  Verbatim copy of
`ShellMink.ChainDataGeom.false_of_ahat_subset_band`, which cannot be imported here (module
docstring).  `rec_p` and `rec_vJ` push a point of `Â_∞` arbitrarily far along `p` and along
`v_J`, so both are `dot m`-null; then `det p v_J = 0`, against
`det_ne_zero_of_dot vJ_ne dot_nJ_vJ dot_nJ_p`. -/
theorem _root_.Nivat.Colle35.ChainDataGeom.false_of_ahat_band {α : Type*} {η xper : Config α}
    {vl p gen : ℤ × ℤ} {S : Finset (ℤ × ℤ)} (cg : ChainDataGeom η xper vl p S gen)
    {m : ℤ × ℤ} (hm : m ≠ 0) {a b : ℤ}
    (hband : ∀ g ∈ ⋃ i, cg.toChainData.Ahat i, a ≤ dot m g ∧ dot m g ≤ b) : False := by
  obtain ⟨g, hg⟩ := cg.ahat_nonempty
  have hdir : ∀ d : ℤ × ℤ,
      (∀ g ∈ ⋃ i, cg.toChainData.Ahat i, g + d ∈ ⋃ i, cg.toChainData.Ahat i) →
      dot m d = 0 := by
    intro d hd
    by_contra hne
    have hk : ∀ k : ℕ, a ≤ dot m g + (k : ℤ) * dot m d ∧ dot m g + (k : ℤ) * dot m d ≤ b := by
      intro k
      have := hband _ (Nivat.ColleReg.ray_of_recession hd hg k)
      rwa [dot_add, Nivat.ColleReg.dot_zsmul_right] at this
    set k : ℕ := (b - a + 1).toNat with hk_def
    have hkge : b - a + 1 ≤ (k : ℤ) := Int.self_le_toNat _
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
    obtain ⟨hlo, hhi⟩ := hk k
    obtain ⟨hlo0, hhi0⟩ := hband g hg
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have : (k : ℤ) * dot m d ≤ -(k : ℤ) := by nlinarith
      omega
    · have : (k : ℤ) ≤ (k : ℤ) * dot m d := by nlinarith
      omega
  have hp : dot m p = 0 := hdir p cg.rec_p
  have hv : dot m cg.vJ = 0 := hdir cg.vJ cg.rec_vJ
  exact Nivat.ColleReg.det_ne_zero_of_dot cg.vJ_ne cg.dot_nJ_vJ cg.dot_nJ_p
    (det_eq_zero_of_dot_eq_zero hm hp hv)

/-- **🔴 A chain with `B (i+1) ⊆ halfStrip (A i) vl` and a finite seed is not a `ChainDataGeom`.**

`subStrip` + `hchain` trap every `A i`, hence every `Â_i = A_i - k_i v_ℓ`, in
`halfStrip (B 0) vl`, on which `det vl` is bounded (`det_bounded_on_halfStrip`); that is a band
for the normal `perp vl`, and `false_of_ahat_band` finishes.  `kk`, `u`, `p`, `shell`, `fill`
are not used.  Compare `tmp/chaindata_kkzero_false.lean`'s `chainDataGeom_kk_zero_false`, which
needs the same `hchain`/`hB0` **plus** `kk ≡ 0`, constant `u`, `p ≠ 0` and `p ∥ vl`. -/
theorem _root_.Nivat.Colle35.ChainDataGeom.false_of_chain_halfStrip {α : Type*}
    {η xper : Config α} {vl p gen : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (cg : ChainDataGeom η xper vl p S gen)
    (hchain : ∀ i, cg.toChainData.B (i + 1) ⊆ Colle35.halfStrip (cg.toChainData.A i) vl)
    (hB0 : (cg.toChainData.B 0).Finite) (hvl : vl ≠ 0) : False := by
  have hstrip : ∀ i, cg.toChainData.A i ⊆ Colle35.halfStrip (cg.toChainData.B 0) vl :=
    chain_subset_halfStrip cg.subStrip hchain
  obtain ⟨M, hM⟩ := det_bounded_on_halfStrip hB0 vl
  have hperp : Nivat.ColleReg.perp vl ≠ 0 := by
    intro h
    apply hvl
    simp only [Nivat.ColleReg.perp, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero,
      neg_eq_zero] at h
    exact Prod.ext h.2 h.1
  refine cg.false_of_ahat_band hperp (a := -M) (b := M) ?_
  intro g hg
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
  rw [cg.AhatEq i] at hi
  have hmem : g + (cg.kk i : ℤ) • vl ∈ Colle35.halfStrip (cg.toChainData.B 0) vl :=
    hstrip i hi
  have hb := hM _ hmem
  rw [det_add_right, Nivat.ColleReg.det_smul_right, det_self, mul_zero, add_zero] at hb
  rw [Nivat.ColleReg.dot_perp]
  exact hb

/-- **🔴 `ChainRecursion`'s chain is never the `B`/`A` of a `ChainDataGeom`** when the seed is
finite — which it is on the route `exists_chainData` serves (every `E(𝒮_φ)`-enveloped set is
finite, `Nivat.L1Sfin.hSfin_of_decompDataZ`, `SfinBound.lean`).  `hchain` is `chainB_succ_eq_chainA` (`rfl`) plus
`subset_halfStrip`; nothing about `kk` or `u` is assumed.  This is
`tmp/stephyp_landing_audit.lean`'s `chainRecursion_forces_kk_nonzero` with `hcgu`, `hkk`, `hp`,
`hpk` all dropped. -/
theorem not_chainDataGeom_of_chainRecursion (ξ xper : Config ℤ) (S : Finset (ℤ × ℤ))
    (vl u₀ : ℤ × ℤ) (hstep : StepHyp ξ xper S vl u₀)
    (B0 : Set (ℤ × ℤ)) (hB0 : EnvOf (↑S : Set (ℤ × ℤ)) B0)
    (hagree0 : ∀ z ∈ B0, T u₀ ξ z = xper z) {p gen : ℤ × ℤ}
    (cg : ChainDataGeom ξ xper vl p S gen)
    (hcgB : cg.toChainData.B = chainB ξ xper S vl u₀ hstep B0 hB0 hagree0)
    (hcgA : cg.toChainData.A = chainA ξ xper S vl u₀ hstep B0 hB0 hagree0)
    (hB0fin : B0.Finite) (hvl : vl ≠ 0) : False := by
  refine cg.false_of_chain_halfStrip ?_ ?_ hvl
  · intro i
    have hEq : cg.toChainData.B (i + 1) = cg.toChainData.A i := by
      rw [hcgB, hcgA]
      exact chainB_succ_eq_chainA ξ xper S vl u₀ hstep B0 hB0 hagree0 i
    rw [hEq]
    exact Nivat.LE2.subset_halfStrip _ vl
  · have h0 : cg.toChainData.B 0 = B0 := by rw [hcgB]; rfl
    exact h0 ▸ hB0fin

/-! ### Transcription guards for the refutation (PROTOCOL §21)

Two guards, so the refutation above can never silently drift into refuting a lookalike:

* `type_of%` pins the *statement* of `not_chainDataGeom_of_chainRecursion` to the current
  disk signatures of `ChainDataGeom`, `chainB`/`chainA` and `StepHyp`; if any of them changes
  upstream this `rfl` fails to elaborate.
* the second `example` *applies the real declaration* to close `False` from exactly its
  hypotheses — it is not a `¬P` about a separately transcribed `P`. -/

example : type_of% @not_chainDataGeom_of_chainRecursion =
    ∀ (ξ xper : Config ℤ) (S : Finset (ℤ × ℤ)) (vl u₀ : ℤ × ℤ)
      (hstep : StepHyp ξ xper S vl u₀) (B0 : Set (ℤ × ℤ))
      (hB0 : EnvOf (↑S : Set (ℤ × ℤ)) B0) (hagree0 : ∀ z ∈ B0, T u₀ ξ z = xper z)
      {p gen : ℤ × ℤ} (cg : ChainDataGeom ξ xper vl p S gen),
      cg.toChainData.B = chainB ξ xper S vl u₀ hstep B0 hB0 hagree0 →
      cg.toChainData.A = chainA ξ xper S vl u₀ hstep B0 hB0 hagree0 →
      B0.Finite → vl ≠ 0 → False := rfl

example (ξ xper : Config ℤ) (S : Finset (ℤ × ℤ)) (vl u₀ : ℤ × ℤ)
    (hstep : StepHyp ξ xper S vl u₀) (B0 : Set (ℤ × ℤ))
    (hB0 : EnvOf (↑S : Set (ℤ × ℤ)) B0) (hagree0 : ∀ z ∈ B0, T u₀ ξ z = xper z)
    {p gen : ℤ × ℤ} (cg : ChainDataGeom ξ xper vl p S gen)
    (hcgB : cg.toChainData.B = chainB ξ xper S vl u₀ hstep B0 hB0 hagree0)
    (hcgA : cg.toChainData.A = chainA ξ xper S vl u₀ hstep B0 hB0 hagree0)
    (hB0fin : B0.Finite) (hvl : vl ≠ 0) : False :=
  not_chainDataGeom_of_chainRecursion ξ xper S vl u₀ hstep B0 hB0 hagree0 cg hcgB hcgA hB0fin hvl

end Nivat.ChainAsm

#print axioms Nivat.ChainAsm.shellFinite_of
#print axioms Nivat.ChainAsm.subShell_of
#print axioms Nivat.ChainAsm.shellSubInf_of
#print axioms Nivat.ChainAsm.shellProper_of
#print axioms Nivat.ChainAsm.fillZero_of
#print axioms Nivat.ChainAsm.fillStep_of
#print axioms Nivat.ChainAsm.shellInfZero_of
#print axioms Nivat.Colle35.ChainDataGeom.ofParts
#print axioms Nivat.Colle35.FaceBlock.generatesAt_a'
#print axioms Nivat.Colle35.latticeConvex_iUnion_hatOf
#print axioms Nivat.ChainAsm.isLatticeConvexRegion_coe
#print axioms Nivat.ChainAsm.envOf_coe_self
#print axioms Nivat.ChainAsm.exists_seed
#print axioms Nivat.ChainAsm.isMaxEnvIn_of_stepHyp
#print axioms Nivat.ChainAsm.hasMaxEnvIn_of_stepHyp
#print axioms Nivat.ChainAsm.hatOf_finite
#print axioms Nivat.ChainAsm.chain_subset_halfStrip
#print axioms Nivat.ChainAsm.det_bounded_on_halfStrip
#print axioms Nivat.Colle35.ChainDataGeom.false_of_ahat_band
#print axioms Nivat.Colle35.ChainDataGeom.false_of_chain_halfStrip
#print axioms Nivat.ChainAsm.not_chainDataGeom_of_chainRecursion
