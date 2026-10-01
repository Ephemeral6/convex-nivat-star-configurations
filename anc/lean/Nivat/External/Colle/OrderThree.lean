/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.AppendixD
import Nivat.External.Colle.AlphabetReduction
import Nivat.Section8.ExternalDefs
import Nivat.External.Colle.DecompData

/-!
# A minimal counterexample has order `≥ 3`

## The question

*"Is there a reason a minimal counterexample cannot have `m = 2` — in the decomposition theory
(`DecompData.lean`), in `MinimalCounterexample`, or in Collé's §4?"*

**Yes.**  The reason is in Collé's §1, not §4, and it is an external citation.
`b3_colle2.txt:180-182`, verbatim:

> **Theorem 1.12 (Szabados [20]).**  Let `η ∈ 𝒜^{ℤ²}`, with `𝒜 ⊂ ℤ`, and suppose
> `η = η₁ + η₂` is a `ℤ`-minimal periodic decomposition.  Then `η` does not have low convex
> complexity.

Theorem 1.12 is **standalone** — it is not conditional on anything Collé proves.  He spends it
at `b3_colle2.txt:230`, inside the proof of Corollary 1.16:

> *"Since Conjecture 1.11 holds for `m = 2` (see Theorem 1.12), we may assume `m ≥ 3`."*

but the exclusion does not depend on that context: a counterexample has low convex complexity
**by definition** (`IsCounterexample`, `Section8/ExternalDefs.lean`), so Theorem 1.12's
conclusion contradicts it outright.

⚠ **How this was nearly missed.**  Searching `Nivat/` by conclusion shape (`2 < _.m`,
`3 ≤ _.m`, `_.m ≠ 2`) comes back empty; every `hm` in the tree is `2 ≤ m`.  That is the wrong
place to look — the fact is not about `m` at all, it is about **order**, and it was already in
the tree under a name containing neither "m" nor "1.12":
`Nivat.not_lowConvexComplexity_of_hasOrder_two` (`AppendixD.lean:2583`, Corollary D.2, no
`sorry`).  Searching for `1\.12|theorem112|Theorem112` — i.e. by *paper notation* — also comes
back empty.  This is CLAUDE.md's recorded failure mode: **按数学内容搜，不按论文记号搜**.

## What was missing, and is supplied here

Corollary D.2 is stated over `Config (ZMod p)` with the `𝔽_p` order `Nivat.HasOrder`
(`AppendixD.lean:2573`).  `IsMinimalCounterexample` (`Section8/ExternalDefs.lean:52`) is over
`Config ℤ` with `Nivat.HasOrderZ` (`:43`).  The bridge needs three things; two were already
in the tree and one was not:

| piece | status before |
|---|---|
| faithful prime reduction `ℤ → ZMod p` | present — `exists_prime_injOn_intCast` (`AlphabetReduction.lean:182`) |
| periodicity reflects along it | present — `isPeriodic_comp_iff` (`AlphabetReduction.lean:169`) |
| **low convex complexity descends along any recolouring** | **absent** — §0 below |

§0 is the missing piece and it needs no injectivity: patterns of `ι ∘ θ` are *images* of
patterns of `θ`, so `P (ι ∘ θ) Q ≤ P θ Q` for every `ι` whatsoever (`P_comp_le`).
Injectivity is spent only on non-periodicity, where `reduceMod_two_spike_Per_ne`
(`AlphabetReduction.lean:340`) shows it is genuinely needed.

## Result, and what it does **not** require

`three_le_of_counterexample` (§2): **every** counterexample to the convex Nivat conjecture has
order `≥ 3` — not only the minimal one.  `three_le_m` (§3): `3 ≤ d.m` for every
`d : DecompDataZ ξ` over a minimal counterexample.

⚠ **No change to `DecompData` is needed, and none is made.**  `DecompData.hm`
(`DecompData.lean:88`) is `2 ≤ m` where the truth is `3 ≤ m`, so strengthening the field was
the obvious move — and it would even have been *free*, since `hm` has no consumer anywhere in
the tree (`grep -rn "\.hm\b|hm :="` in `Nivat/` finds the declaration `:88`, its docstring
`:210` and the constructor `:314`, and **no projection**).  But free is not the same as
necessary: §3 shows `3 ≤ d.m` follows from `hξ` and `d` alone, both of which every consumer
already holds, so the structure, its sole producer
(`DecompDataZ.of_minimalCounterexample`, `DecompData.lean:277`) and every downstream file stay
untouched.  This follows CLAUDE.md's **加强，不替换**: the bound is *added* alongside, not
edited into, the existing definition.

The one situation that would bring the field edit back: a consumer holding a bare `DecompData`
**without** `hξ`.  None exists today — the only consumer path is `ColleRegion.lean:366`, which
carries `hξ` — but `three_le_m` cannot serve such a consumer if one appears.

Consumers that ask for `2 ≤ m` (`exists_two_nonparallel_edge_normals`, `EdgeNormals.lean:38`;
`generatingSet_no_edge_parallel`, `MinkowskiEdges.lean:484`) keep working unchanged either way.

## Why this matters for leaf A's shell block

At `m = 2`, `b3_colle2.txt:432` forces `J = ι+1`, and the `2m`-gon's antipodal edge relation
forces `−v_{ℓ_{J+1}} = +v_{ℓ_ι} = v_ℓ`: Collé's two sweep directions coincide and `:518`
degenerates to a single sweep, which the scratch refutations
`shell518_identity_collapse` / `model_identity_witness_infinite`
(`tmp/shellsubinf_twodir.lean`) and `shellSubStrip_free_of_parallel`
(`tmp/shellsubstrip_twofactor.lean`) rule out.  With `m ≥ 3` that branch is **unreachable**, so
leaf A owes no separate `m = 2` argument and the two-factor shell object is live everywhere
reachable.

⚠ Those two `tmp/` files are scratch and are **not** in the build; they are cited as the
provenance of the `m = 2` obstruction, not as dependencies.  Nothing in this file depends on
them.

⚠ This file does **not** prove `w₁ ∦ v_ℓ`, and — corrected 2026-09-18 — **it must not**, because
that statement is false where it matters and its negation is what the shell block needs.

The arithmetic: writing `J+1 = ι+k`, `w₁ = −v_{ℓ_{J+1}}` is parallel to `v_ℓ = v_{ℓ_ι}` iff
`k ≡ 0` or `k ≡ m (mod 2m)`, and on the admissible range `k ∈ [2,m]` given by
`b3_colle2.txt:432` the unique solution is `k = m`, i.e. `J = ι+m−1`, where
`w₁ = −v_{ℓ_{ι+m}} = +v_{ℓ_ι} = v_ℓ` at **every** `m ≥ 2`.

An earlier revision of this docstring called that index *bad*.  It is the opposite:
`halfStrip B vl` (`LatticeEdges.lean:1810-1811`) is closed under **adding** `vl`, so
`ChainData.shellSubStrip` (`Lemma35.lean:743`) — which asks a `w₁`-sweep to stay in that
half-strip up to the `kk i` shift — is satisfiable **exactly when `w₁ = +v_ℓ`**.  So the
parallelism is not an obstruction to be cleared, it is the condition that **pins `J = ι+m−1`**,
and it is available at every `m ≥ 2`.  The sign is the whole content here and it was got
backwards once; the half-strip's closure direction is the thing to re-check first.

What `m ≥ 3` buys is therefore about the *other* direction, not this one: at `J = ι+m−1`,
`ChainDataWithShell.shellInf_eq` (`ChainShell.lean:58-59`) pins `vJ1 = v_{ℓ_{J−1}} =
v_{ℓ_{ι+m−2}}`, and `ι+m−2 ≢ ι, ι+m (mod 2m)` exactly when `m ≥ 3`.  So `m ≥ 3` is what keeps
Collé's two sweep directions **distinct** — which is the content of the previous paragraph, and
the whole reason this file exists.

## Hypothesis ledger

Nothing is assumed beyond `IsCounterexample ξ` and its own fields.  No hypothesis is carried
that is not consumed: `hfin` feeds the prime choice *and* `patterns_finite_of_range_finite`;
`hpos` kills order `0`; `hnp` kills order `1` and feeds the `𝔽_p` non-periodicity; `hlow`
feeds Corollary D.2.
-/

set_option autoImplicit false

namespace Nivat.OrderThree

open Nivat Nivat.Colle.AlphabetReduction

/-! ## 0. Low convex complexity descends along an arbitrary recolouring

The missing bridge piece.  No injectivity, no ring structure, no finiteness of the target
alphabet: the pattern set of `ι ∘ θ` is the image of the pattern set of `θ`. -/

/-- The patterns of a recoloured configuration are the recoloured patterns. -/
theorem patterns_comp {α β : Type*} (ι : α → β) (θ : Config α) (Q : Finset (ℤ × ℤ)) :
    patterns (fun z => ι (θ z)) Q
      = (fun g : Q → α => fun q : Q => ι (g q)) '' patterns θ Q := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨pattern θ Q u, ⟨u, rfl⟩, rfl⟩
  · rintro ⟨g, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, rfl⟩

/-- **`P` is monotone under recolouring.**  Companion to `P_mono` (`Defs/Complexity.lean:73`),
which is monotonicity in the *window*; this is monotonicity in the *alphabet map*.  The
finiteness hypothesis is on `θ`'s range, not on the alphabet, because `P` is an `ncard` and
`Set.ncard_image_le` needs the source finite — `Config ℤ` has an infinite alphabet, which is
exactly the situation `patterns_finite_of_range_finite` (`Defs/Complexity.lean:55`) was
written for. -/
theorem P_comp_le {α β : Type*} (ι : α → β) {θ : Config α} (hfin : (Set.range θ).Finite)
    (Q : Finset (ℤ × ℤ)) : P (fun z => ι (θ z)) Q ≤ P θ Q := by
  rw [P, P, patterns_comp]
  exact Set.ncard_image_le (patterns_finite_of_range_finite hfin Q)

/-- **Low convex complexity descends along any recolouring.**  The same window `S` works. -/
theorem lowConvexComplexity_comp {α β : Type*} (ι : α → β) {θ : Config α}
    (hfin : (Set.range θ).Finite) (h : LowConvexComplexity θ) :
    LowConvexComplexity (fun z => ι (θ z)) := by
  obtain ⟨S, hne, hconv, hP⟩ := h
  exact ⟨S, hne, hconv, le_trans (P_comp_le ι hfin S) hP⟩

/-- The `reduceMod` form.  `reduceMod p ξ` is definitionally `fun z => ((ξ z : ℤ) : ZMod p)`
(`AlphabetReduction.lean:213`). -/
theorem lowConvexComplexity_reduceMod {ξ : Config ℤ} (hfin : (Set.range ξ).Finite)
    (h : LowConvexComplexity ξ) (p : ℕ) :
    LowConvexComplexity (reduceMod p ξ) :=
  lowConvexComplexity_comp (fun a : ℤ => (a : ZMod p)) hfin h

/-! ## 1. The `𝔽_p` order of a faithful reduction -/

/-- Non-periodicity reflects along a faithful reduction.  This is the one step that needs
injectivity; `reduceMod_two_spike_Per_ne` (`AlphabetReduction.lean:340`) refutes it without. -/
theorem not_isPeriodic_reduceMod {ξ : Config ℤ} {p : ℕ}
    (hinj : Set.InjOn (fun a : ℤ => (a : ZMod p)) (Set.range ξ))
    (h : ¬ IsPeriodic ξ) : ¬ IsPeriodic (reduceMod p ξ) :=
  fun hc => h ((isPeriodic_comp_iff hinj).mp hc)

/-- A `ℤ`-decomposition of length `n` reduces to an `𝔽_p`-decomposition of length `n`. -/
theorem periodicDecomp_reduceMod {ξ : Config ℤ} {n : ℕ} (p : ℕ)
    (hdec : PeriodicDecompZ ξ n) : PeriodicDecomp (reduceMod p ξ) n := by
  obtain ⟨f, hper, hsum⟩ := hdec
  refine ⟨fun i => reduceMod p (f i), fun i => ?_, fun z => ?_⟩
  · obtain ⟨u, hu, hu0⟩ := hper i
    exact ⟨u, mem_Per_reduceMod p hu, hu0⟩
  · show ((ξ z : ℤ) : ZMod p) = ∑ i, ((f i z : ℤ) : ZMod p)
    rw [hsum z]
    exact map_sum (Int.castRingHom (ZMod p)) (fun i => f i z) Finset.univ

/-- A configuration with a periodic decomposition of length `≤ 1` is periodic.  Length `0`
makes it identically zero. -/
theorem isPeriodic_of_periodicDecomp_le_one {p : ℕ} {x : Config (ZMod p)} {k : ℕ}
    (hk : k ≤ 1) (h : PeriodicDecomp x k) : IsPeriodic x := by
  obtain ⟨f, hper, hsum⟩ := h
  interval_cases k
  · refine ⟨((1 : ℤ), (0 : ℤ)), ?_, ?_⟩
    · rw [mem_Per_iff]
      funext z
      show x (z + ((1 : ℤ), (0 : ℤ))) = x z
      rw [hsum, hsum]
      simp
    · intro hc
      exact absurd (congrArg Prod.fst hc) (by norm_num)
  · obtain ⟨u, hu, hu0⟩ := hper 0
    refine ⟨u, ?_, hu0⟩
    rw [mem_Per_iff]
    funext z
    show x (z + u) = x z
    rw [hsum, hsum]
    simp only [Fin.sum_univ_one]
    exact Per.apply hu z

/-- **The `𝔽_p` order of a faithful reduction of an order-`2` configuration is `2`.** -/
theorem hasOrder_reduceMod_two {ξ : Config ℤ} {p : ℕ}
    (hdec : PeriodicDecompZ ξ 2) (hnp : ¬ IsPeriodic (reduceMod p ξ)) :
    HasOrder (reduceMod p ξ) 2 := by
  refine ⟨periodicDecomp_reduceMod p hdec, fun k hk => ?_⟩
  by_contra hlt
  exact hnp (isPeriodic_of_periodicDecomp_le_one (by omega) hk)

/-! ## 2. Order `2` is impossible for a counterexample -/

/-- **`b3_colle2.txt:180-182` (Szabados, Theorem 1.12), transported to `ℤ`.**  No
counterexample to the convex Nivat conjecture has order `2`. -/
theorem not_hasOrderZ_two_of_counterexample {ξ : Config ℤ} (hc : IsCounterexample ξ) :
    ¬ HasOrderZ ξ 2 := by
  obtain ⟨hfin, -, hnp, hlow⟩ := hc
  rintro ⟨hdec, -⟩
  obtain ⟨p, hp, hinj⟩ := exists_prime_injOn_intCast hfin
  have : Fact p.Prime := ⟨hp⟩
  exact not_lowConvexComplexity_of_hasOrder_two
    (hasOrder_reduceMod_two hdec (not_isPeriodic_reduceMod hinj hnp))
    (lowConvexComplexity_reduceMod hfin hlow p)

/-- **Every counterexample has order at least `3`.**

Order `0` contradicts `0 < ξ z`; order `1` makes `ξ` periodic; order `2` is Szabados.
Stated for an arbitrary counterexample, not only a minimal one — which is why it retires the
`m = 2` branch outright rather than only at the minimum. -/
theorem three_le_of_counterexample {ξ : Config ℤ} (hc : IsCounterexample ξ) {n : ℕ}
    (hn : HasOrderZ ξ n) : 3 ≤ n := by
  by_contra hcon
  have hlt : n < 3 := by omega
  interval_cases n
  · obtain ⟨⟨f, -, hsum⟩, -⟩ := hn
    have h0 := hc.2.1 0
    rw [hsum 0, Fin.sum_univ_zero] at h0
    exact lt_irrefl _ h0
  · obtain ⟨⟨f, hper, hsum⟩, -⟩ := hn
    obtain ⟨u, hu, hu0⟩ := hper 0
    refine hc.2.2.1 ⟨u, ?_, hu0⟩
    rw [mem_Per_iff]
    funext z
    show ξ (z + u) = ξ z
    rw [hsum, hsum]
    simp only [Fin.sum_univ_one]
    exact Per.apply hu z
  · exact not_hasOrderZ_two_of_counterexample hc hn

/-- The order of a minimal counterexample is `≥ 3`. -/
theorem three_le_order_of_minimalCounterexample {ξ : Config ℤ}
    (hξ : IsMinimalCounterexample ξ) : ∃ n, HasOrderZ ξ n ∧ 3 ≤ n := by
  obtain ⟨hc, n, hn, -⟩ := hξ
  exact ⟨n, hn, three_le_of_counterexample hc hn⟩

/-! ## 3. `3 ≤ d.m` for **every** `d`, with no change to `DecompData`

`DecompData` already carries a `PeriodicDecompZ ξ m` in its fields (`eta`, `h`, `h_period`,
`h_ne`, `sum_eq`), so **minimality of the order bounds `d.m` from below no matter where `d`
came from**.  Combined with `three_le_of_counterexample`, that gives `3 ≤ d.m` from the two
arguments that `exists_chainData` (`RegionSteps.lean:810`) and `region_case1` (`:1132`)
already take, with no new field, no producer change and no wiring. -/

/-- A `DecompDataZ` **is** a periodic decomposition of length `m`; the fields are already
there (`DecompData.lean:87-95`: `eta`, `h`, `sum_eq`, `h_ne`, `h_period`). -/
theorem periodicDecompZ_of_decompDataZ {ξ : Config ℤ} (d : Nivat.Colle35.DecompDataZ ξ) :
    PeriodicDecompZ ξ d.toDecompData.m :=
  ⟨d.toDecompData.eta,
    fun i => ⟨d.toDecompData.h i, d.toDecompData.h_period i, d.toDecompData.h_ne i⟩,
    d.toDecompData.sum_eq⟩

/-- **`3 ≤ d.m`, for every `d : DecompDataZ ξ` over a minimal counterexample.**

Note it does not depend on `d` having come from `of_minimalCounterexample`: the order's own
minimality clause (`HasOrderZ`, `Section8/ExternalDefs.lean:43`, second conjunct) bounds
`d.m` below for *any* `d` whatsoever. -/
theorem three_le_m {ξ : Config ℤ} (hξ : IsMinimalCounterexample ξ)
    (d : Nivat.Colle35.DecompDataZ ξ) : 3 ≤ d.toDecompData.m := by
  obtain ⟨hc, n, hn, -⟩ := hξ
  exact le_trans (three_le_of_counterexample hc hn)
    (hn.2 _ (periodicDecompZ_of_decompDataZ d))

end Nivat.OrderThree
