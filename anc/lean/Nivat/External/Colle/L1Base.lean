/-
Copyright (c) 2026 Nivat formalisation project. All rights reserved.
-/
import Nivat.External.Colle.L1RegionBuild
import Nivat.External.Colle.L1Prim
import Nivat.External.Colle.Lemma45
import Nivat.External.Colle.DirectionRigidity

/-!
# `L1Base` — the induction scaffold for `ofWedge`'s `hbase` (leaf L1 / Claim 4.6)

`Nivat.ColleReg.ofWedge` (`L1RegionBuild.lean:344`) needs
`hbase : Colle41.PeriodOn (T e ξ) (chainFull B vl u' b₀ 0) (c • vl)`.  team-lead's judgment
request (2026-09-19, `ofWedge` vs. Claim 4.6) established that this slice is **not** small: it
extends unboundedly forward along `u'`.  This file isolates exactly why, and reduces `hbase`
to one Collé-flavoured hypothesis.

## The reduction, in one sentence

`dot (expNormal u' vl) u' = 0` (`L1RegionBuild.lean:295`, unconditional) means translating by
`u'` never changes which side of the cut a point is on. So the level-`0` slice is *literally*
a plain forward `u'`-sweep of a bounded band:

```
chainFull B vl u' b₀ 0 = sweep band0 u'      where  band0 := fullSweep B vl ∩ halfPlaneGE …
```

(`chainFull_zero_eq_sweep_band0` below, pure algebra — no `ξ`, no periodicity, no Collé
content). This is exactly the shape Claim 4.6 propagates: a period known on a bounded seed
(`band0`), pushed forward one `u'`-step at a time, forever.

## The scaffold (Collé-independent) vs. the step (Collé's content)

`Colle41.PeriodOn x U h := ∀ z ∈ U, z + h ∈ U → x (z+h) = x z` is *overlap-only*
(`Lemma41.lean:659`), so it passes to **monotone** unions for free
(`Nivat.L1Region.periodOn_iUnion_of_monotone`, already in the tree). `cumSweep K w t` below is
the cumulative version of `sweep` (`∃ s ≤ t`, not `∃ t` alone) — monotone in `t` by
construction, with `⋃ t, cumSweep K w t = sweep K w` (`iUnion_cumSweep_eq_sweep`, pure algebra).

So the *only* non-mechanical content left is the single step

```
∀ t, PeriodOn x (cumSweep K w t) h → PeriodOn x (cumSweep K w (t + 1)) h
```

— propagating periodicity one `w`-layer further out. `periodOn_sweep_of_step` packages
"base case + this step, for all `t`" into "periodic on the whole sweep" by plain `Nat.rec` plus
the monotone-union lemma; it takes the step as a named hypothesis, not a proof, per team-lead's
instruction to land the scaffold and expose the step as a single bindable obligation.

## What this file does *not* claim

`periodOn_sweep_of_step`'s hypothesis, if it held **unconditionally for every `t`**, would
make `wedgeFull` itself `c • vl`-periodic (since `chainFull … 0 = sweep band0 u'` and — once
`band0`'s periodicity is chosen as `c • vl`-periodicity — the whole argument goes through to
`wedgeFull`), contradicting `ofWedge`'s other field `hinf`. This is not a bug: it is the
Lean mirror of why Collé's own induction does **not** run forever — the paper's actual
Claim 4.6 argument (mod-`p` reduction, Lemma 2.5/2.6) presumably produces the step for only
finitely many `t`, or produces a *different*, weaker per-step conclusion whose accumulation
stabilises. **This file does not resolve that; it only proves the reduction is exact and
supplies the bookkeeping**, so whoever attacks the step next attacks exactly one `t → t+1`
statement, not a 16-conjunct blob.
-/

set_option autoImplicit false

namespace Nivat.L1Base

open Nivat Nivat.Colle41 Nivat.RegionSweep Nivat.LE2 Nivat.ColleReg

/-! ## §1  Cumulative sweep: a monotone version of `sweep` -/

/-- The cumulative forward sweep: points reachable from `K` by *at most* `t` steps of `w`.
Monotone in `t` by construction (`cumSweep_mono`), unlike `sweep K w` itself (a union of
*disjoint-looking* translates `K + s•w`, not obviously ordered). -/
def cumSweep (K : Set (ℤ × ℤ)) (w : ℤ × ℤ) (t : ℕ) : Set (ℤ × ℤ) :=
  {z | ∃ g ∈ K, ∃ s : ℕ, s ≤ t ∧ z = g + (s : ℤ) • w}

theorem mem_cumSweep {K : Set (ℤ × ℤ)} {w z : ℤ × ℤ} {t : ℕ} :
    z ∈ cumSweep K w t ↔ ∃ g ∈ K, ∃ s : ℕ, s ≤ t ∧ z = g + (s : ℤ) • w := Iff.rfl

theorem cumSweep_mono (K : Set (ℤ × ℤ)) (w : ℤ × ℤ) : Monotone (cumSweep K w) := by
  intro a b hab z hz
  obtain ⟨g, hg, s, hs, rfl⟩ := hz
  exact ⟨g, hg, s, hs.trans hab, rfl⟩

theorem cumSweep_zero (K : Set (ℤ × ℤ)) (w : ℤ × ℤ) : cumSweep K w 0 = K := by
  ext z
  constructor
  · rintro ⟨g, hg, s, hs, rfl⟩
    have : s = 0 := Nat.le_zero.mp hs
    subst this
    simpa using hg
  · intro hz
    exact ⟨z, hz, 0, le_refl 0, by simp⟩

theorem subset_cumSweep (K : Set (ℤ × ℤ)) (w : ℤ × ℤ) (t : ℕ) : K ⊆ cumSweep K w t := by
  intro z hz
  exact ⟨z, hz, 0, Nat.zero_le t, by simp⟩

/-- **The point of `cumSweep`**: its union over `t` is exactly the plain (non-cumulative)
`sweep`, so nothing is lost by working with the monotone version. -/
theorem iUnion_cumSweep_eq_sweep (K : Set (ℤ × ℤ)) (w : ℤ × ℤ) :
    (⋃ t, cumSweep K w t) = sweep K w := by
  ext z
  simp only [Set.mem_iUnion, mem_cumSweep, mem_sweep]
  constructor
  · rintro ⟨t, g, hg, s, -, rfl⟩
    exact ⟨g, hg, s, rfl⟩
  · rintro ⟨g, hg, s, rfl⟩
    exact ⟨s, g, hg, s, le_refl s, rfl⟩

/-! ## §2  The scaffold: base + single step ⟹ periodic on the whole sweep

This is the entire non-Collé content: `PeriodOn` passes to monotone unions
(`Nivat.L1Region.periodOn_iUnion_of_monotone`), and `cumSweep` turns `sweep` into a monotone
union with an explicit `t = 0` base layer. -/

/-- **The scaffold.**  Given periodicity on the seed `K` and a single-step propagation
hypothesis (bindable, and refutable independently of everything else here), periodicity holds
on the whole forward sweep `sweep K w`. -/
theorem periodOn_sweep_of_step {A : Type*} {x : Config A} {K : Set (ℤ × ℤ)} {w h : ℤ × ℤ}
    (hbase : PeriodOn x K h)
    (hstep : ∀ t : ℕ, PeriodOn x (cumSweep K w t) h → PeriodOn x (cumSweep K w (t + 1)) h) :
    PeriodOn x (sweep K w) h := by
  rw [← iUnion_cumSweep_eq_sweep]
  apply Nivat.L1Region.periodOn_iUnion_of_monotone (cumSweep_mono K w)
  intro t
  induction t with
  | zero => rw [cumSweep_zero]; exact hbase
  | succ n ih => exact hstep n ih

/-! ## §3  Instantiating at `ofWedge`'s level-`0` slice

`chainFull B vl u' b₀ 0` is, up to the algebra below, exactly `sweep band0 u'` for the bounded
band `band0`.  The equality uses only `dot_expNormal_u' : dot (expNormal u' vl) u' = 0`
(`L1RegionBuild.lean:295`) — translating by any multiple of `u'` never changes which side of
the `expNormal`-cut a point sits on, in either direction. -/

/-- The bounded band that `chainFull B vl u' b₀ 0` is a plain `u'`-sweep of: `fullSweep B vl`
(the doubly-infinite `vl`-extension of `B`) cut at the level-`0` half-plane. -/
noncomputable def band0 (B : Set (ℤ × ℤ)) (vl u' b₀ : ℤ × ℤ) : Set (ℤ × ℤ) :=
  fullSweep B vl ∩ halfPlaneGE (expNormal u' vl) (expLevel u' vl b₀ 0)

/-- **The reduction.**  Pure algebra: `chainFull B vl u' b₀ 0` is exactly the plain forward
`u'`-sweep of `band0`, using only `dot_expNormal_u' = 0` (no unimodularity, no `ξ`). -/
theorem chainFull_zero_eq_sweep_band0 (B : Set (ℤ × ℤ)) (vl u' b₀ : ℤ × ℤ) :
    Nivat.ColleReg.chainFull B vl u' b₀ 0 = sweep (band0 B vl u' b₀) u' := by
  ext z
  simp only [Nivat.ColleReg.chainFull, Nivat.L1Region.cut, Set.mem_inter_iff, mem_sweep,
    band0, wedgeFull]
  constructor
  · rintro ⟨⟨g, hg, t, rfl⟩, hlev⟩
    have hdot : dot (expNormal u' vl) (g + (t : ℤ) • u') = dot (expNormal u' vl) g := by
      rw [dot_add, dot_smul_right, dot_expNormal_u']
      ring
    refine ⟨g, ⟨hg, ?_⟩, t, rfl⟩
    simp only [halfPlaneGE, Set.mem_ofPred_eq] at hlev ⊢
    rwa [hdot] at hlev
  · rintro ⟨g, ⟨hg, hglev⟩, t, rfl⟩
    have hdot : dot (expNormal u' vl) (g + (t : ℤ) • u') = dot (expNormal u' vl) g := by
      rw [dot_add, dot_smul_right, dot_expNormal_u']
      ring
    refine ⟨⟨g, hg, t, rfl⟩, ?_⟩
    simp only [halfPlaneGE, Set.mem_ofPred_eq] at hglev ⊢
    rwa [hdot]

/-- **`hbase`, reduced to one step.**  Combines `periodOn_sweep_of_step` with the reduction
above: periodicity on `band0` plus the single `t → t+1` propagation step gives exactly
`ofWedge`'s `hbase` obligation. The step is left as a named hypothesis — this is `L1Base`'s
entire deliverable, per team-lead's "(a) scaffold in the main tree, (b) named single-step
binder" split. -/
theorem hbase_of_step {ξ : Config ℤ} {e vl u' b₀ : ℤ × ℤ} {B : Set (ℤ × ℤ)} {c : ℤ}
    (hbase0 : PeriodOn (T e ξ) (band0 B vl u' b₀) (c • vl))
    (hstep : ∀ t : ℕ,
      PeriodOn (T e ξ) (cumSweep (band0 B vl u' b₀) u' t) (c • vl) →
      PeriodOn (T e ξ) (cumSweep (band0 B vl u' b₀) u' (t + 1)) (c • vl)) :
    PeriodOn (T e ξ) (Nivat.ColleReg.chainFull B vl u' b₀ 0) (c • vl) := by
  rw [chainFull_zero_eq_sweep_band0]
  exact periodOn_sweep_of_step hbase0 hstep

/-! ## §4  `(b)`, stated precisely (not proved)

2026-09-19: Aface refuted four naive shapes of `hstep` above (`L1Prim.lean` §6,
`not_forall_periodOn_of_overlap` / `_of_eq_union_shift` / `_iUnion` / `_of_determined`) — the
bare implication `PeriodOn (cumSweep t) → PeriodOn (cumSweep (t+1))` is, per those
counterexamples, not something a direct argument from "new points are determined by a fixed
offset from old ones" can establish. What closes the gap is `Nivat.L1Prim.
periodOn_of_copy_of_invariant` (`L1Prim.lean:417`, proved, four lines): the *old* layer must be
`h`-invariant (`∀ z, z + h ∈ U ↔ z ∈ U`), not merely periodic.

**Reading (Aface's, not re-derived by me — flagged per §15):** in Collé's actual chain this
invariance holds because `h ∥ ℓ` and every region is a union of complete `ℓ`-lines, so the
content that must survive into this induction is the *line structure* of the layers
(`band0`/`cumSweep` are unions of full `u'`-shifted copies of `band0`, and `h = c • vl` — the
candidate invariant direction is `vl`, not `u'`, so `hinv` below is genuinely about `band0`'s
shape along `vl`, still open).

`hbase_of_copy_step` restates `hbase_of_step` with `hstep` replaced by its precise
decomposition: an invariance hypothesis `hinv`, plus the determination data `hwin`/`hcopy` from
`periodOn_of_copy_of_invariant`, one `w : ℕ → ℤ × ℤ` offset per layer. Nothing here is proved
beyond wiring — `hinv`/`hwin`/`hcopy` are exactly `(b)`, now three named obligations instead of
one opaque implication. -/

/-- **§14 撤回标注（2026-09-19，team-lead 裁决）**：`hinv`/copy-invariance 不是 Claim 4.6
的路线，本定理逻辑上仍然合法（前提不可满足不等于定理错），但**不是 (b) 该有的形状**，
被 Lemma 2.6 路线取代——留作参考，不删，不再推进。

理由（Aface `L1Prim.lean` §8 内核实测）：`dot_expNormal_vl`（`L1RegionBuild.lean:288`，需
`hunimod`）给出 `dot (expNormal u' vl) vl = 1`，这逼出 `hinv`（沿 `c • vl` 对
`cumSweep … u' t` 不变）当且仅当 `c = 0`（`not_invariant_of_dot_eq_one`）；而 `ofWedge`
另一字段 `hinf` 逼出 `c ≠ 0`（`ne_zero_of_not_periodOn_smul`）。两者矛盾，`hinv` 对 L1
用例不可满足。team-lead 的裁决（先判「改用 `hinv` 形状」，见到 Aface 的量化反例后当场
撤回）正式确立了 PROTOCOL.md §25：一条 `¬∀` 只能否掉一条通路，评估具体实例可证性必须
直接量那个实例，不能从 `¬∀` 外推。 -/
theorem hbase_of_copy_step {ξ : Config ℤ} {e vl u' b₀ : ℤ × ℤ} {B : Set (ℤ × ℤ)} {c : ℤ}
    (hbase0 : PeriodOn (T e ξ) (band0 B vl u' b₀) (c • vl))
    (w : ℕ → ℤ × ℤ)
    (hinv : ∀ t : ℕ, ∀ z : ℤ × ℤ,
      z + c • vl ∈ cumSweep (band0 B vl u' b₀) u' t ↔ z ∈ cumSweep (band0 B vl u' b₀) u' t)
    (hwin : ∀ t : ℕ, ∀ z ∈ cumSweep (band0 B vl u' b₀) u' (t + 1),
      z ∉ cumSweep (band0 B vl u' b₀) u' t → z + w t ∈ cumSweep (band0 B vl u' b₀) u' t)
    (hcopy : ∀ t : ℕ, ∀ z ∈ cumSweep (band0 B vl u' b₀) u' (t + 1),
      z ∉ cumSweep (band0 B vl u' b₀) u' t →
      (T e ξ) z = (T e ξ) (z + w t)) :
    PeriodOn (T e ξ) (Nivat.ColleReg.chainFull B vl u' b₀ 0) (c • vl) := by
  refine hbase_of_step hbase0 fun t ht => ?_
  exact Nivat.L1Prim.periodOn_of_copy_of_invariant (hinv t) ht (hwin t) (hcopy t)

/-! ## §5  Lemma 2.6 (Szabados), ℤ-coefficient case, in call-site shape

`b3_colle2.txt:311`: "Let `η ∈ 𝒜^{ℤ²}` be a configuration and suppose
`φ(X)=(X^{h_1}-1)⋯(X^{h_m}-1) ∈ ann_R(η)`, where `h_1,…,h_m ∈ ℤ²` are vectors in pairwise
distinct directions. If `ℓ ∈ nexpl(η)`, then `ℓ` contains some vector `h_i`, with `1≤i≤m`."

This is a **wrapper, not new mathematics**: `Nivat.Colle.exists_tangent_of_orbit_halfPlane_ambiguity`
(`DirectionRigidity.lean:79`, already proved, on-chain via `Generating.lean:1`) is the same
statement with `ℓ ∈ Colle45.NonExpansiveLine ξ` unpacked into its four raw components
(`x`, `y`, `hx : x ∈ orbitClosure ξ`, `hy`, `hne : x ≠ y`, `hagree`) and with the integer `dot`
used by `NonExpansiveLine`/everywhere else in this codebase replaced by the real-valued
`inner2` it was originally proved with. Repacking those two differences (`NonExpansiveLine`'s
definition, `inner2_toReal`/`dot_neg_left` for the cast) is all this theorem does.

⚠ **This is the `R = ℤ` case only.** Claim 4.6's actual use of Lemma 2.6 (`b3_colle2.txt:792`)
needs `R = ZMod p` (`φ_ι ∈ ann_{ℤ_p}(η - η̄_{ι₀})`), which is a genuinely different statement:
`Nivat.kari_szabados_decomp'` (`KSDecomposition.lean:271`), the machinery this wrapper's proof
ultimately rests on, is stated and proved only for `Config ℤ`. That gap is tracked separately;
this theorem does not close it. -/

/-- **Lemma 2.6 (Szabados), `R = ℤ` case**, restated in the exact membership shape used at
every other call site in this codebase (`ℓ ∈ Colle45.NonExpansiveLine ξ`), instead of the raw
existential `DirectionRigidity.lean` states it with. -/
theorem lemma26_int {n : ℕ} {h : Fin n → ℤ × ℤ}
    (hnp : Pairwise fun i j => det (h i) (h j) ≠ 0)
    {ξ : Config ℤ}
    (hann : act (∏ i, (mono (h i) - 1) : LaurentTwo ℤ) ξ = 0)
    {ℓ : ℤ × ℤ} (hℓ_nel : ℓ ∈ Nivat.Colle45.NonExpansiveLine ξ) :
    ∃ i, dot ℓ (h i) = 0 := by
  obtain ⟨-, x, y, hx, hy, hne, hagree⟩ := hℓ_nel
  have hagree' : ∀ z : ℤ × ℤ, (0 : ℝ) ≤ inner2 (toReal (-ℓ)) z → x z = y z := by
    intro z hz
    refine hagree z ?_
    show dot ℓ z ≤ 0
    rw [inner2_toReal, dot_neg_left] at hz
    have : (dot ℓ z : ℝ) ≤ 0 := by push_cast at hz; linarith
    exact_mod_cast this
  obtain ⟨i, hi⟩ := Nivat.Colle.exists_tangent_of_orbit_halfPlane_ambiguity hnp hx hy hne hagree'
    (v := h) (hann := hann)
  refine ⟨i, ?_⟩
  rw [inner2_toReal, dot_neg_left] at hi
  have : (dot ℓ (h i) : ℝ) = 0 := by push_cast at hi; linarith
  exact_mod_cast this

end Nivat.L1Base

#print axioms Nivat.L1Base.lemma26_int
#print axioms Nivat.L1Base.cumSweep_mono
#print axioms Nivat.L1Base.cumSweep_zero
#print axioms Nivat.L1Base.subset_cumSweep
#print axioms Nivat.L1Base.iUnion_cumSweep_eq_sweep
#print axioms Nivat.L1Base.periodOn_sweep_of_step
#print axioms Nivat.L1Base.chainFull_zero_eq_sweep_band0
#print axioms Nivat.L1Base.hbase_of_step
#print axioms Nivat.L1Base.hbase_of_copy_step
