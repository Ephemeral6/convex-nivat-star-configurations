/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Section8.ExternalDefs
import Nivat.External.Colle.Lemma35Wiring
import Nivat.External.Colle.Generating

/-!
# `region_not_periodic` was FALSE as extracted

## Outcome, 2026-09-16 (r67 verdict) — read this first

The header below used to end "…and stays false under every natural repair".  **That claim is
withdrawn.**  It was measured against three re-added hypotheses only (`xper ∈ orbitClosure ξ`,
`¬ IsPeriodic ξ`, `hc_grow`) and never against the one the extraction actually dropped:
`hξ : IsMinimalCounterexample ξ`, which *was* in scope at the hole inside `colle_region`.

The witness below does not satisfy it.  `IsCounterexample` (`Section8/ExternalDefs.lean:49`)
demands `∀ z, 0 < ξ z`, and `xiD (-1,-1) = 0` — proved below as `xiD_not_minimalCounterexample`.
`hξ` has been restored to the signature in `RegionSteps.lean`; the leaf is **open, not
refuted**.

What survives, and is still the sharpest thing in this file, is the observation in "Why it
fails" that `¬ IsPeriodic ϑ` is strictly stronger than the "no fully periodic accumulation
point" of Colle's Claim 3.7.  Whether `hξ` closes that distance is not settled here.  Note
that the conclusion may not simply be weakened to match Claim 3.7: `colle_region` exports
`¬ IsPeriodic ξ'` verbatim and `FirstHalfPlane.lean:1352,1365,1376` consumes it three times.

## The statement at issue (as extracted, without `hξ`)

```lean
theorem region_not_periodic {ξ xper ϑ : Config ℤ} {vl p gen : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (c : ChainData ξ xper vl S gen) {K ε : ℕ}
    (hc_env : c.Env = Nivat.LE2.EnvOf (S : Set (ℤ × ℤ)))
    (hgen : Nivat.Colle.GeneratesAt ξ S gen)
    (hvl_ne : vl ≠ 0) (hp_ne : p ≠ 0) (hdet_vl : det p vl = 0)
    (hϑ_mem : ϑ ∈ orbitClosure ξ)
    (hagree : ∀ z ∈ ⋃ i, c.Ahat i, ϑ z = T ((K : ℤ) • vl) xper z)
    (hϑ_periodic : PeriodicOnWith ϑ (⋃ i, c.Ahat i) p)
    (hshell : ∀ z ∈ c.shellInf ε, ϑ z = T ((K : ℤ) • vl) xper z)
    (hshell_not : ¬ (∀ z ∈ c.shellInf (ε + 1), ϑ z = T ((K : ℤ) • vl) xper z)) :
    ¬ IsPeriodic ϑ
```

This file does **not** prove it.  It proves the negation of its universal closure
(`region_not_periodic_refuted`), and in fact the negation of the *strengthened* statement
that also assumes everything `colle_region` has available at the call site but did not pass
in (`region_not_periodic_refuted_strong`):

* `xper ∈ orbitClosure ξ` — a hypothesis of `Nivat.Colle35.lemma35` that this extraction
  dropped;
* `¬ IsPeriodic ξ` — available from `IsMinimalCounterexample ξ`;
* `∀ i, c.B i ⊂ c.B (i + 1)` — the `hc_grow` that `region_nonempty` and
  `region_periods_and_rays` do take.

So the hole cannot be closed by adding any of those back, and it cannot be closed from
`c.maximalHat`: **`maximalHat` is satisfied by the witness below**, non-vacuously and
sharply (`cD_maximalHat_is_sharp`), by the same wall mechanism as `Nivat.Colle35.chainB`.

## Why it fails

`ϑ` is constrained only by `ϑ ∈ orbitClosure ξ`, agreement with `x̂_per := T (K • vl) xper`
on `Â_∞` and on `Â_∞^{(ε)}`, one disagreement on `Â_∞^{(ε+1)}`, and `PeriodicOnWith ϑ Â_∞ p`.
Orbit closures of aperiodic configurations routinely contain periodic configurations, and
nothing in that list excludes one.  `maximalHat` governs how far the *region* can be
extended; it says nothing about the period group of `ϑ`.

And the source does not claim otherwise.  In arXiv:1909.08195v4 §3, the paragraph after
(3.5), Colle proves **Claim 3.7**: the set `{T^{t v_{ℓ'}} ϑ : t ∈ ℤ_+}` has no *fully*
periodic accumulation points.  He never asserts that `ϑ` has no period at all.  `IsPeriodic`
here is `∃ u ∈ Per f, u ≠ 0` (`Nivat/Defs/Config.lean:119`) — a *single* nonzero period — so
`¬ IsPeriodic ϑ` is strictly stronger than "not fully periodic", which is all §3 delivers
and all §3 uses.  The extracted obligation therefore asks for more than the paper proves.

## The witness

Write `[P]` for `if P then (1 : ℤ) else 0`.

| object | value |
| --- | --- |
| `ξ` | `fun z => [0 ≤ z.1] + [0 ≤ z.2]` — aperiodic, annihilated by `(X^{(1,0)}-1)(X^{(0,1)}-1)` |
| `xper` | `fun z => [0 ≤ z.2]` — in `orbitClosure ξ` (push the vertical wall to `-∞`) |
| `ϑ` | `fun z => [2 ≤ z.1] + 1` — in `orbitClosure ξ` (push the horizontal wall to `+∞`), period `(0,1)` |
| `vl`, `p` | `(1,0)`, `(1,0)` |
| `S`, `gen` | the four points of `sq1`; `(1,1)` |
| `K`, `ε` | `0`, `0` |
| `B i = A i` | `box (0,0) (1+i, 1)` — strictly growing |
| `k_i`, `u_i` | `i`, `(-2-i, 0)` |
| `Â_i` | `box (-i,0) (1,1)`, so `Â_∞ = {z | z.1 ≤ 1, 0 ≤ z.2 ≤ 1}` |
| `Â_i^{(ε)}` | `box (-i,0) (1+ε,1)`; `Â_∞^{(ε)} = {z | z.1 ≤ 1+ε, 0 ≤ z.2 ≤ 1}` |
| `Env` | `Nivat.LE2.EnvOf ↑S` (the real envelope predicate) |

`ξ (z + k_i v_ℓ + u_i) = ξ (z - (2,0)) = [2 ≤ z.1] + [0 ≤ z.2]` while
`x_per (z + k_i v_ℓ) = [0 ≤ z.2]`: the two agree exactly on `{z.1 ≤ 1}`.  That wall, cut
against the half-strip `H_{B_i}(ℓ) - k_i v_ℓ = {z.1 ≥ -i, 0 ≤ z.2 ≤ 1}`, is *exactly* `Â_i`
— which is why `maximalHat` is true here and not vacuous.  `Â_∞^{(0)} = Â_∞` carries
agreement; `Â_∞^{(1)}` contains `(2,0)`, where `ϑ (2,0) = 2 ≠ 1 = x̂_per (2,0)`.  That is
(3.1).  And `ϑ` has period `(0,1)`.

`GeneratesAt ξ S gen` is genuine, not vacuous: every member of `orbitClosure ξ` obeys
`x (1,1) + x (0,0) = x (1,0) + x (0,1)` (`rule_of_mem_orbitClosure`), which determines the
value at `(1,1)` from the other three points of `sq1`.

## Status

No `sorry`, no new `axiom`, no `native_decide`.  The target theorem is **not** present in
this file, because it is false.
-/

namespace Nivat.ColleStep

open Nivat Nivat.Colle Nivat.Colle35 Nivat.LE2

/-! ## Small toolkit -/

theorem mem_box_mk {a b c d : ℤ} {z : ℤ × ℤ} :
    z ∈ box (a, b) (c, d) ↔ a ≤ z.1 ∧ z.1 ≤ c ∧ b ≤ z.2 ∧ z.2 ≤ d := Iff.rfl

/-- `n • (1,0) = (n,0)`, the shape in which `kk i • vl` keeps appearing. -/
@[simp] theorem smul_vl (n : ℤ) : n • ((1 : ℤ), (0 : ℤ)) = (n, 0) := by
  simp [Prod.ext_iff]

/-! ## The window -/

/-- The generating window: the four lattice points of `sq1`. -/
def winS : Finset (ℤ × ℤ) :=
  {((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ)), ((1 : ℤ), (1 : ℤ))}

theorem coe_winS : (winS : Set (ℤ × ℤ)) = sq1 := by
  ext z
  obtain ⟨a, b⟩ := z
  simp only [winS, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, sq1, box, Set.mem_setOf_eq, Prod.mk.injEq]
  omega

theorem gen_mem_winS : ((1 : ℤ), (1 : ℤ)) ∈ winS := by decide

/-- Every non-degenerate box is `E(↑winS)`-enveloped. -/
theorem env_box {a b c d : ℤ} (h1 : a < c) (h2 : b < d) :
    EnvOf (winS : Set (ℤ × ℤ)) (box (a, b) (c, d)) := by
  rw [coe_winS]
  exact LE2.envOf_sq1_box (by exact h1) (by exact h2)

/-! ## The configurations -/

/-- `ξ`.  Sum of two half-plane indicators in transverse directions: aperiodic, and
annihilated by `(X^{(1,0)} - 1)(X^{(0,1)} - 1)`. -/
def xiD : Config ℤ := fun z => (if 0 ≤ z.1 then 1 else 0) + (if 0 ≤ z.2 then 1 else 0)

/-- `x_per`: the vertical wall of `xiD` pushed to `-∞`.  Lies in `orbitClosure xiD`. -/
def xperD : Config ℤ := fun z => if 0 ≤ z.2 then 1 else 0

/-- `ϑ`: the horizontal wall of `xiD` pushed to `+∞`, with the vertical wall left standing
at `z.1 = 2`.  Lies in `orbitClosure xiD`, and has period `(0,1)`. -/
def thetaD : Config ℤ := fun z => (if 2 ≤ z.1 then 1 else 0) + 1

theorem xiD_apply (z : ℤ × ℤ) :
    xiD z = (if 0 ≤ z.1 then 1 else 0) + (if 0 ≤ z.2 then 1 else 0) := rfl

theorem xperD_apply (z : ℤ × ℤ) : xperD z = if 0 ≤ z.2 then 1 else 0 := rfl

theorem thetaD_apply (z : ℤ × ℤ) : thetaD z = (if 2 ≤ z.1 then 1 else 0) + 1 := rfl

/-! ### `ξ` is aperiodic -/

/-- **`ξ` has no nonzero period.**  So the witness survives the hypothesis `¬ IsPeriodic ξ`.

It does *not* survive the full `IsMinimalCounterexample ξ` that is in scope at the call site;
see `xiD_not_minimalCounterexample` below. -/
theorem xiD_not_isPeriodic : ¬ IsPeriodic xiD := by
  rintro ⟨u, hu, hne⟩
  rw [mem_Per_iff] at hu
  have key : ∀ x y : ℤ,
      (if 0 ≤ x + u.1 then (1 : ℤ) else 0) + (if 0 ≤ y + u.2 then (1 : ℤ) else 0)
        = (if 0 ≤ x then (1 : ℤ) else 0) + (if 0 ≤ y then (1 : ℤ) else 0) := by
    intro x y
    have h := congrFun hu (x, y)
    simpa [xiD] using h
  obtain ⟨b, hb1, hb2⟩ : ∃ b : ℤ, b < 0 ∧ b + u.2 < 0 :=
    ⟨min 0 (-u.2) - 1, by omega, by omega⟩
  obtain ⟨a, ha1, ha2⟩ : ∃ a : ℤ, a < 0 ∧ a + u.1 < 0 :=
    ⟨min 0 (-u.1) - 1, by omega, by omega⟩
  have e1 := key 0 b
  have e2 := key (-1) b
  have e3 := key a 0
  have e4 := key a (-1)
  have hu1 : u.1 = 0 := by split_ifs at e1 e2 <;> omega
  have hu2 : u.2 = 0 := by split_ifs at e3 e4 <;> omega
  exact hne (by simp [Prod.ext_iff, hu1, hu2])

/-! ### `ξ` is **not** a minimal counterexample — the limit of this refutation

Added 2026-09-16 (r67 verdict).  `IsCounterexample` (`Section8/ExternalDefs.lean:48-49`) is
`(Set.range ξ).Finite ∧ (∀ z, 0 < ξ z) ∧ ¬ IsPeriodic ξ ∧ LowConvexComplexity ξ`.  The witness
clears the third conjunct (above) but fails the second at a single point, which is enough:
restoring `hξ : IsMinimalCounterexample ξ` to `region_not_periodic` — where it was in scope
all along — makes every theorem in this file inapplicable to the repaired statement. -/

theorem xiD_not_counterexample : ¬ IsCounterexample xiD := by
  rintro ⟨-, hpos, -, -⟩
  have h := hpos ((-1 : ℤ), (-1 : ℤ))
  simp [xiD] at h

/-- **The repaired `region_not_periodic` is untouched by this file.**  `hξ` excludes the
witness, so the refutations below bound only the stripped extraction. -/
theorem xiD_not_minimalCounterexample : ¬ IsMinimalCounterexample xiD :=
  fun h => xiD_not_counterexample h.1

/-! ### Orbit-closure memberships -/

theorem xperD_mem_orbitClosure : xperD ∈ orbitClosure xiD := by
  intro W
  obtain ⟨M, hM⟩ := (W.image (fun w : ℤ × ℤ => w.1)).exists_le
  refine ⟨(-M - 1, 0), fun w hw => ?_⟩
  have hw1 : w.1 ≤ M := hM w.1 (Finset.mem_image_of_mem _ hw)
  simp only [xiD_apply, xperD_apply, Prod.fst_add, Prod.snd_add]
  split_ifs <;> omega

theorem thetaD_mem_orbitClosure : thetaD ∈ orbitClosure xiD := by
  intro W
  obtain ⟨M, hM⟩ := (W.image (fun w : ℤ × ℤ => -w.2)).exists_le
  refine ⟨(-2, M), fun w hw => ?_⟩
  have hw2 : -w.2 ≤ M := hM (-w.2) (Finset.mem_image_of_mem _ hw)
  simp only [xiD_apply, thetaD_apply, Prod.fst_add, Prod.snd_add]
  split_ifs <;> omega

/-- **`ϑ` is periodic**, with period `(0,1)`. -/
theorem thetaD_isPeriodic : IsPeriodic thetaD := by
  refine ⟨((0 : ℤ), (1 : ℤ)), ?_, by simp [Prod.ext_iff]⟩
  rw [mem_Per_iff]
  funext z
  simp [T, thetaD_apply]

/-! ### The generating window is genuine -/

/-- Every member of `orbitClosure ξ` obeys the local rule of `(X^{(1,0)}-1)(X^{(0,1)}-1)`. -/
theorem rule_of_mem_orbitClosure {x : Config ℤ} (hx : x ∈ orbitClosure xiD) :
    x (1, 1) + x (0, 0) = x (1, 0) + x (0, 1) := by
  obtain ⟨u, hu⟩ := hx {((1 : ℤ), (1 : ℤ)), ((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (1 : ℤ))}
  rw [hu ((1 : ℤ), (1 : ℤ)) (by decide), hu ((0 : ℤ), (0 : ℤ)) (by decide),
    hu ((1 : ℤ), (0 : ℤ)) (by decide), hu ((0 : ℤ), (1 : ℤ)) (by decide)]
  simp only [xiD_apply, Prod.fst_add, Prod.snd_add]
  ring

theorem generatesAt_xiD : GeneratesAt xiD winS ((1 : ℤ), (1 : ℤ)) := by
  refine ⟨gen_mem_winS, fun x hx y hy hagree => ?_⟩
  have hx' := rule_of_mem_orbitClosure hx
  have hy' := rule_of_mem_orbitClosure hy
  have e0 : x ((0 : ℤ), (0 : ℤ)) = y ((0 : ℤ), (0 : ℤ)) := hagree _ (by decide)
  have e1 : x ((1 : ℤ), (0 : ℤ)) = y ((1 : ℤ), (0 : ℤ)) := hagree _ (by decide)
  have e2 : x ((0 : ℤ), (1 : ℤ)) = y ((0 : ℤ), (1 : ℤ)) := hagree _ (by decide)
  omega

/-! ## The `ChainData` witness -/

/-- A complete `ChainData` for `ξ = xiD`, `x_per = xperD`, `v_ℓ = (1,0)`, window `winS`,
distinguished point `(1,1)`.  All nineteen fields are discharged; `maximalHat` holds by the
wall at `z.1 = 2` of `xiD` seen through the translation `u_i`, exactly as in
`Nivat.Colle35.chainB`. -/
def cD : ChainData xiD xperD ((1 : ℤ), (0 : ℤ)) winS ((1 : ℤ), (1 : ℤ)) := by
  refine {
    Env := EnvOf (winS : Set (ℤ × ℤ))
    B := fun i => box (0, 0) (1 + (i : ℤ), 1)
    A := fun i => box (0, 0) (1 + (i : ℤ), 1)
    u := fun i => (-2 - (i : ℤ), 0)
    kk := fun i => i
    Ahat := fun i => box (-(i : ℤ), 0) (1, 1)
    shell := fun i ε => box (-(i : ℤ), 0) (1 + (ε : ℤ), 1)
    shellInf := fun ε => {z : ℤ × ℤ | z.1 ≤ 1 + (ε : ℤ) ∧ 0 ≤ z.2 ∧ z.2 ≤ 1}
    fill := fun i i₀ ε _ =>
      box (-(i : ℤ), 0) (1, 1) ∪ box (-(i₀ : ℤ), 0) (1 + (ε : ℤ), 1)
    envB := ?_
    envA := ?_
    subBA := ?_
    subAB := ?_
    subStrip := ?_
    agreeA := ?_
    AhatEq := ?_
    AhatMono := ?_
    maximalHat := ?_
    shellFinite := ?_
    subShell := ?_
    shellSubInf := ?_
    shellInfZero := ?_
    -- `I₀`（第 162 轮，`b3_colle2.txt:520`）：本实例的 shell 字段都不看 `i` 的下界，取 0。
    I₀ := 0
    shellSubStrip := ?_
    shellProper := ?_
    shellEnv := ?_
    fillZero := ?_
    fillStep := ?_
    fillCover := ?_ }
  -- envB
  · exact fun i => env_box (by omega) (by omega)
  -- envA
  · exact fun i => env_box (by omega) (by omega)
  -- subBA
  · exact fun i => subset_rfl
  -- subAB
  · intro i z hz
    simp only [mem_box_mk] at hz ⊢
    push_cast
    omega
  -- subStrip
  · exact fun i => Nivat.Colle35.subset_halfStrip _ _
  -- agreeA : ξ (z + u i) = x_per z on A i
  · intro i z hz
    simp only [mem_box_mk] at hz
    simp only [xiD_apply, xperD_apply, Prod.fst_add, Prod.snd_add]
    split_ifs <;> omega
  -- AhatEq
  · intro i
    ext z
    simp only [smul_vl, Set.mem_setOf_eq, mem_box_mk, Prod.fst_add, Prod.snd_add]
    omega
  -- AhatMono
  · intro i j hij z hz
    simp only [mem_box_mk] at hz ⊢
    have : (i : ℤ) ≤ (j : ℤ) := by exact_mod_cast hij
    omega
  -- maximalHat : the wall cuts the half-strip down to exactly Â_i
  · intro i Tset _henv _hsub hstrip hag z hz
    have h1 := hstrip hz
    have h2 := hag z hz
    simp only [Set.mem_setOf_eq, smul_vl] at h1
    obtain ⟨b, hb, t, heq⟩ := h1
    simp only [mem_box_mk] at hb
    simp only [smul_vl, Prod.ext_iff, Prod.fst_add, Prod.snd_add] at heq
    have ht : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
    simp only [smul_vl, xiD_apply, xperD_apply, Prod.fst_add, Prod.snd_add,
      Prod.mk_add_mk] at h2
    simp only [mem_box_mk]
    split_ifs at h2 <;> omega
  -- shellFinite
  · exact fun i ε => finite_box _ _
  -- subShell
  · intro i ε z hz
    simp only [mem_box_mk] at hz ⊢
    omega
  -- shellSubInf
  · intro i ε z hz
    simp only [mem_box_mk] at hz
    simp only [Set.mem_setOf_eq]
    omega
  -- shellInfZero
  · intro z hz
    simp only [Set.mem_setOf_eq] at hz
    refine Set.mem_iUnion.mpr ⟨(-z.1).toNat, ?_⟩
    simp only [mem_box_mk]
    push_cast at hz
    omega
  -- shellSubStrip
  · intro ε _ _ _ i _ z hz
    simp only [mem_box_mk] at hz
    simp only [Set.mem_setOf_eq, smul_vl]
    refine ⟨(0, z.2), ?_, (z.1 + (i : ℤ)).toNat, ?_⟩
    · simp only [mem_box_mk]
      omega
    · simp only [smul_vl, Prod.ext_iff, Prod.fst_add, Prod.snd_add, and_true, true_and]
      omega
  -- shellProper
  · intro ε _i₀ hε _hEnv i _hi hsub
    have hmem : ((1 + (ε : ℤ), (0 : ℤ)) : ℤ × ℤ) ∈ box (-(i : ℤ), (0 : ℤ)) (1 + (ε : ℤ), 1) := by
      simp only [mem_box_mk]
      omega
    have h := hsub hmem
    simp only [mem_box_mk] at h
    omega
  -- shellEnv
  · exact ⟨1, 0, by norm_num, fun i _ => by
      simpa using env_box (a := -(i : ℤ)) (b := 0) (c := 1 + ((1 : ℕ) : ℤ)) (d := 1)
        (by omega) (by omega)⟩
  -- fillZero
  · exact fun i i₀ ε => subset_rfl
  -- fillStep
  · exact fun i i₀ ε n z hz => Or.inl hz
  -- fillCover.  Round 80 (`Lemma35.lean:765`) rephrased this field against
  -- `Colle37.GenClosure`; here the filtration is constant (`fillStep` is `Or.inl`), so the
  -- old `⟨0, …⟩` index becomes a bare `GenClosure.base`.
  · intro ε i₀ _hε _hEnv i _hi z hz
    simp only [mem_box_mk] at hz
    refine Nivat.Colle37.GenClosure.base ?_
    by_cases h : z.1 ≤ 1
    · exact Or.inl (by simp only [mem_box_mk]; omega)
    · exact Or.inr (by simp only [mem_box_mk]; omega)

/-! ### Readable projections -/

theorem cD_env : cD.Env = EnvOf (winS : Set (ℤ × ℤ)) := rfl

theorem cD_B (i : ℕ) : cD.B i = box (0, 0) (1 + (i : ℤ), 1) := rfl

theorem cD_Ahat (i : ℕ) : cD.Ahat i = box (-(i : ℤ), 0) (1, 1) := rfl

theorem cD_kk (i : ℕ) : cD.kk i = i := rfl

theorem cD_u (i : ℕ) : cD.u i = (-2 - (i : ℤ), 0) := rfl

theorem cD_shellInf (ε : ℕ) :
    cD.shellInf ε = {z : ℤ × ℤ | z.1 ≤ 1 + (ε : ℤ) ∧ 0 ≤ z.2 ∧ z.2 ≤ 1} := rfl

theorem cD_iUnion_Ahat :
    (⋃ i, cD.Ahat i) = {z : ℤ × ℤ | z.1 ≤ 1 ∧ 0 ≤ z.2 ∧ z.2 ≤ 1} := by
  ext z
  simp only [Set.mem_iUnion, cD_Ahat, mem_box_mk, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, _, h2, h3, h4⟩
    exact ⟨h2, h3, h4⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(-z.1).toNat, by omega, h1, h2, h3⟩

/-! ### The chain grows strictly -/

/-- The witness satisfies `hc_grow`: the chain is strictly increasing, so the counterexample
survives that hypothesis too. -/
theorem cD_grow (i : ℕ) : cD.B i ⊂ cD.B (i + 1) := by
  rw [Set.ssubset_def]
  refine ⟨?_, ?_⟩
  · intro z hz
    simp only [cD_B, mem_box_mk] at hz ⊢
    push_cast
    omega
  · intro hsub
    have hmem : ((2 + (i : ℤ), (0 : ℤ)) : ℤ × ℤ) ∈ cD.B (i + 1) := by
      simp only [cD_B, mem_box_mk]
      push_cast
      simp only [and_true, true_and]
      omega
    have h := hsub hmem
    simp only [cD_B, mem_box_mk] at h
    omega

/-! ### `maximalHat` is non-vacuous and sharp -/

/-- **The maximality hypothesis does real work here.**  The box one column wider than `Â_0`
is `E(↑S)`-enveloped, contains `Â_0`, and still sits inside the half-strip: the *only*
premise of `maximalHat` it fails is the agreement clause.  So `maximalHat` is neither
vacuous nor slack in this witness — and `ϑ` is periodic all the same. -/
theorem cD_maximalHat_is_sharp :
    cD.Env (box (0, 0) (2, 1)) ∧
      cD.Ahat 0 ⊆ box (0, 0) (2, 1) ∧
      box (0, 0) (2, 1) ⊆ {z : ℤ × ℤ |
        z + ((cD.kk 0 : ℤ) • ((1 : ℤ), (0 : ℤ))) ∈
          Nivat.Colle35.halfStrip (cD.B 0) ((1 : ℤ), (0 : ℤ))} ∧
      ¬ (∀ z ∈ box (0, 0) (2, 1),
          xiD (z + ((cD.kk 0 : ℤ) • ((1 : ℤ), (0 : ℤ)) + cD.u 0))
            = xperD (z + (cD.kk 0 : ℤ) • ((1 : ℤ), (0 : ℤ)))) := by
  refine ⟨cD_env ▸ env_box (by norm_num) (by norm_num), ?_, ?_, ?_⟩
  · intro z hz
    simp only [cD_Ahat, mem_box_mk] at hz ⊢
    omega
  · intro z hz
    simp only [mem_box_mk] at hz
    simp only [Set.mem_setOf_eq, cD_kk, cD_B, Nat.cast_zero, smul_vl]
    refine ⟨(0, z.2), ?_, z.1.toNat, ?_⟩
    · simp only [mem_box_mk]
      omega
    · simp only [smul_vl, Prod.ext_iff, Prod.fst_add, Prod.snd_add, and_true, true_and]
      omega
  · intro hall
    have h := hall ((2 : ℤ), (0 : ℤ)) (by simp only [mem_box_mk]; norm_num)
    simp only [cD_kk, cD_u, Nat.cast_zero, smul_vl, xiD_apply, xperD_apply,
      Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at h
    norm_num at h

/-! ## The refutations -/

/-- **The strengthened statement is false.**  Even with `xper ∈ orbitClosure ξ`,
`¬ IsPeriodic ξ` and strict growth of the chain added as extra hypotheses, the conclusion
`¬ IsPeriodic ϑ` does not follow. -/
theorem region_not_periodic_refuted_strong :
    ¬ (∀ (ξ xper ϑ : Config ℤ) (vl p gen : ℤ × ℤ) (S : Finset (ℤ × ℤ))
        (c : ChainData ξ xper vl S gen) (K ε : ℕ),
        c.Env = Nivat.LE2.EnvOf (S : Set (ℤ × ℤ)) →
        Nivat.Colle.GeneratesAt ξ S gen →
        vl ≠ 0 → p ≠ 0 → det p vl = 0 →
        ϑ ∈ orbitClosure ξ →
        (∀ z ∈ ⋃ i, c.Ahat i, ϑ z = T ((K : ℤ) • vl) xper z) →
        PeriodicOnWith ϑ (⋃ i, c.Ahat i) p →
        (∀ z ∈ c.shellInf ε, ϑ z = T ((K : ℤ) • vl) xper z) →
        ¬ (∀ z ∈ c.shellInf (ε + 1), ϑ z = T ((K : ℤ) • vl) xper z) →
        xper ∈ orbitClosure ξ →
        ¬ IsPeriodic ξ →
        (∀ i, c.B i ⊂ c.B (i + 1)) →
        ¬ IsPeriodic ϑ) := by
  intro h
  refine (h xiD xperD thetaD ((1 : ℤ), (0 : ℤ)) ((1 : ℤ), (0 : ℤ)) ((1 : ℤ), (1 : ℤ)) winS
      cD 0 0 (by rw [cD_env, coe_winS]) generatesAt_xiD
      (by simp [Prod.ext_iff]) (by simp [Prod.ext_iff]) (by simp [det])
      thetaD_mem_orbitClosure ?_ ?_ ?_ ?_
      xperD_mem_orbitClosure xiD_not_isPeriodic cD_grow) thetaD_isPeriodic
  -- hagree
  · intro z hz
    rw [cD_iUnion_Ahat] at hz
    simp only [Set.mem_setOf_eq] at hz
    simp only [T, Nat.cast_zero, zero_smul, add_zero, thetaD_apply, xperD_apply]
    split_ifs <;> omega
  -- hϑ_periodic
  · refine ⟨by simp [Prod.ext_iff], fun g hg hg' => ?_⟩
    rw [cD_iUnion_Ahat] at hg hg'
    simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add] at hg hg'
    simp only [thetaD_apply, Prod.fst_add]
    split_ifs <;> omega
  -- hshell
  · intro z hz
    simp only [cD_shellInf, Set.mem_setOf_eq, Nat.cast_zero] at hz
    simp only [T, Nat.cast_zero, zero_smul, add_zero, thetaD_apply, xperD_apply]
    split_ifs <;> omega
  -- hshell_not
  · intro hall
    have h2 := hall ((2 : ℤ), (0 : ℤ)) (by
      simp only [cD_shellInf, Set.mem_setOf_eq]
      norm_num)
    simp only [T, Nat.cast_zero, zero_smul, add_zero, thetaD_apply, xperD_apply] at h2
    norm_num at h2

/-- **The statement as frozen in `RegionSteps.lean` is false.**  Immediate from
`region_not_periodic_refuted_strong`: the frozen statement has *fewer* hypotheses, so it
implies the strengthened one. -/
theorem region_not_periodic_refuted :
    ¬ (∀ (ξ xper ϑ : Config ℤ) (vl p gen : ℤ × ℤ) (S : Finset (ℤ × ℤ))
        (c : ChainData ξ xper vl S gen) (K ε : ℕ),
        c.Env = Nivat.LE2.EnvOf (S : Set (ℤ × ℤ)) →
        Nivat.Colle.GeneratesAt ξ S gen →
        vl ≠ 0 → p ≠ 0 → det p vl = 0 →
        ϑ ∈ orbitClosure ξ →
        (∀ z ∈ ⋃ i, c.Ahat i, ϑ z = T ((K : ℤ) • vl) xper z) →
        PeriodicOnWith ϑ (⋃ i, c.Ahat i) p →
        (∀ z ∈ c.shellInf ε, ϑ z = T ((K : ℤ) • vl) xper z) →
        ¬ (∀ z ∈ c.shellInf (ε + 1), ϑ z = T ((K : ℤ) • vl) xper z) →
        ¬ IsPeriodic ϑ) :=
  fun h => region_not_periodic_refuted_strong
    (fun ξ xper ϑ vl p gen S c K ε h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 _ _ _ =>
      h ξ xper ϑ vl p gen S c K ε h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)

end Nivat.ColleStep
