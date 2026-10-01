/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Lemma41
import Nivat.External.Colle.GeneratingPatterns
import Nivat.External.Colle.LatticeEdges
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Colle, Claim 4.3 — the sweep induction

Formalisation of the sweep-induction engine of Claim 4.3 in
Cleber F. Colle, *On periodic decompositions, one-sided nonexpansive directions and
Nivat's conjecture*, arXiv:1909.08195 **v4**, §4.  (Also published as DCDS **43** (2023)
4299–4327, where the §4 numbering is shifted by `+1`; this file uses arXiv v4 numbering.)

## Claim 4.3 (arXiv v4, verbatim)

> If `x|(𝒯 + r h') = x|(𝒯 + s h')` holds for some `0 ≤ r < s`, then the restriction of `x`
> to the half strip `ℋ(ℓ_{Q'}) ∩ ℛ ∩ ℋ(−ℓ_{𝒯 + r h'})` is periodic of period `(s − r) h'`.

The proof, verbatim: the coincidence set of `x` and `T^{(s−r)h'} x` contains
`(H_Q − ι h) ∪ (H_𝒯 + r h')` for every `ι ∈ ℕ` (equation (4.4)); one then sets
`ℓ₀ := ℓ_{𝒯 + r h'}` and `ℓ_{i+1} := ℓ_i^{(−)}`, and *"since the convex set
`ℓ₁ ∩ (H_Q − ι h)` has at least `|𝒮 ∩ ℓ_𝒮| − 1` elements and `𝒮` is an `η`-generating
set, from (4.4) we can, by induction, enlarge the set where `x` and `T^{(s−r)h'} x`
coincide by including a subset of `ℓ₁ ∩ ℛ`, which can be as large as we want"*.  The
same idea is then applied to `ℓ₂, …, ℓ_M = ℓ_{Q'}`.

## What this file proves

The **induction itself is fully formalised and `sorry`-free**.  In this file:

* §2 `between_mem` — lattice-convex regions are closed under betweenness along a lattice
  direction.  (Replaces the convexity plumbing that the previous version of this file got
  wrong.)
* §3 `agree_at_of_generatesAt` — one generating-window step: if the punctured window
  `𝒮 \ {a}`, translated so that `a` sits at the target point, lands in a set where `x`
  and `y` already agree, then `x` and `y` agree at the target.  This is Colle's
  "`𝒮` is an `η`-generating set, so from (4.4) we can enlarge the coincidence set".
* §3 `sweep_induction` — that step iterated along one line by strong induction: the
  conquered set grows to the whole enumerated ray.  This is the inner induction of
  Claim 4.3.
* §3 `line_sweep_along` — `sweep_induction` in the concrete form `g₀ + j·w`.
* §4 `multi_line_sweep` — the **outer** induction over the lines `ℓ₀, ℓ₁, …`: each line
  may use the seed set together with *all strictly earlier lines* and the earlier points
  of its own line.  This is Colle's "the same idea applied to the lines `ℓ_i` for
  `i = 2, …, M`".
* §5 `agree_T_on_halfStripFrom` — the seed (4.4): one `q`-step periodicity on the
  half-strip iterates to agreement of `x` with `T^{(n q) v_{ℓ'}} x` on the half-strip,
  for every `n`.
* §5 `claim43_periodOn_of_sweep` — the sweep output converted back into `PeriodOn`.
* §6 `ray_closure_of_period` — periodicity closes an agreement window of length `c`
  along the **forward** ray (index type `ℕ`).
* §7 `hsweep_of_sweepData` — **the full `hsweep` hypothesis of
  `Nivat.Colle41.lemma41_of_sweep` is discharged** from a `SweepData` bundle, with no
  `sorry`.
* §8 the pigeonhole gap `0 < t'₀ ≤ P_η(𝒯) + 1` (`exists_bounded_repeat`).
* §9 non-vacuity **and non-circularity**: `sweep_engine_fires` runs the engine on a
  concrete configuration with a genuinely two-point window (`Swin_erase_nonempty`),
  deriving agreement at infinitely many points from a one-point seed;
  `sweepData_config_indep` shows `SweepData` does not constrain `x` at all.
* §10 the companion pair for `SweepData`: `sweep_covers_not_derivable` /
  `sweep_covers_failure_gives_False` (data failing only the `covers` field, and the
  falsehood that granting `covers` for it would yield) and `goodSweepData` /
  `goodSweepData_periodOn` / `goodSweepData_hsweep` (data satisfying every field, on which
  the engine runs and outputs a true periodicity).
* §11 `exists_sweepData_is_false` and `claim43_hsweep_is_false` — kernel-checked refutations
  of what used to be the file's two *output* statements.  Both were withdrawn on 2026-09-16
  (§7); these refutations are the record of why.

## Why this is not circular

`SweepData` (§7) is purely geometric: none of its fields mentions the configuration `x`.
`sweepData_config_indep` (§9) is the machine-checked witness — the whole bundle transports
verbatim from any `x` to any other.  In particular the `covers` and `window` fields cannot
be the periodicity conclusion of Claim 4.3 in disguise; the `PeriodOn` output of
`hsweep_of_sweepData` is manufactured by the induction of §3–§4 out of the one-direction
seed `hqper`.  `goodSweepData_hsweep` (§10) runs the whole pipeline on concrete data.

### Correction: `covers` was wrongly removed, and had to be reinstated

An intermediate version of this file deleted `covers` from `SweepData`, on the grounds that
"the coverage property is precisely the geometric core of Claim 4.3, so assuming it as part
of the input data concealed the gap", and replaced it by a standalone theorem
`sweepData_covers` carrying a `sorry`.  **The statement that refactoring left behind is
false, not merely unproved.**  With `covers` removed, nothing relates `enum` to `K`, so
`enum` may enumerate a single point while `K` is all of `ℤ²`, with `window` satisfied by a
genuinely two-point generating window over a genuine half-strip seed
(`sweep_covers_not_derivable`, §10).  Worse, granting the deleted statement for that data
and feeding it to the `sorry`-free `claim43_periodOn_of_sweep` yields
`PeriodOn rowConfig ℤ² (0,1)`, which is false (`sweep_covers_failure_gives_False`, §10);
so during that interval `hsweep_of_sweepData` and `claim43_hsweep` were false theorems
held up by a `sorry` standing in for a falsehood.

`covers` is therefore a field again.  This restores exactly the previous division of
labour: the debt is `exists_sweepData`, which must construct `covers` along with the rest.
Colle's proof does the same — the lines `ℓ₀, ℓ₁ := ℓ₀^{(−)}, …, ℓ_M = ℓ_{Q'}` exhaust the
half strip `ℋ(ℓ_{Q'}) ∩ ℛ ∩ ℋ(−ℓ_{𝒯+rh'})` *by construction*, so coverage is part of
building the lines, not a consequence of sweeping them.

**Signature change**, before and after:

    -- before (intermediate version): SweepData had 11 fields, ending at
    window : ∀ i j : ℕ, ∀ z ∈ S.erase a, z + (enum i j - a) ∈ …
    theorem sweepData_covers (d : SweepData η x u u' R B t₁ q) :
        d.K ⊆ halfStripFrom B u' t₁ ∪ (⋃ i, Set.range (d.enum i)) := by sorry

    -- after: the 12th field is back, and `sweepData_covers` is its projection
    covers : K ⊆ halfStripFrom B u' t₁ ∪ (⋃ i, Set.range (enum i))
    theorem sweepData_covers (d : SweepData η x u u' R B t₁ q) :
        d.K ⊆ halfStripFrom B u' t₁ ∪ (⋃ i, Set.range (d.enum i)) := d.covers

The statement of `sweepData_covers` is unchanged character for character; only its
provenance is.  No mathematics was proved by this change — the gap moved back into
`exists_sweepData`, where it was before, and where §10 shows it is at least consistent.

## What is *not* proved

Nothing in this file is now open, but that is a statement about the file, not about Claim 4.3.
The sweep **induction** is complete and fires on concrete data (`goodSweepData_hsweep`, §10.2).
The sweep **construction** — producing a `SweepData` for an arbitrary configuration — is not
here, and the statement that used to assert it (`exists_sweepData`) was withdrawn on
2026-09-16 because §11 refutes it.  §7 records what a correctly stated replacement would
need; the short version is that items 1–4 there are real missing mathematics, and item 2 (the
`(ℓ,ℓ')`-region construction of Claim 4.6/4.11) is a separate open gap elsewhere in this
repository.

### Why the statements were false, not merely unproved

An earlier reading of this file treated `exists_sweepData` as an unfinished construction and
named item 2 as "the binding constraint".  That reading was wrong.  `SweepData` carries the
field `generates : GeneratesAt η S a`, but `exists_sweepData` quantified over every `η`
subject only to `x ∈ orbitClosure η` — it never assumed `η` *has* a generating window.  Colle
gets one from the standing low-complexity hypothesis of Lemma 4.1 via Lemma 2.3; that
hypothesis was absent from the signature.  So the binding constraint on the *stated* theorem
was a missing hypothesis, and no amount of geometry would have discharged it.

`Nivat.Colle43.exists_sweepData_is_false` (§11) is the kernel-checked refutation, at
`η = x = deltaConfig` (the indicator of `(0,0)`), whose orbit closure contains both the
all-zero configuration and the indicator of `{a}` for every `a`, so no finite window
generates.  The witness is **non-degenerate**: `R = ℤ²`, `B = {(0,0)}`, `t₁ = q = 1`, and
`hqper` genuinely true rather than vacuous.  The region data (`K`, `isRegion`, `nonempty`,
`covers`) is never reached.

`claim43_hsweep` — the statement advertised as ready to be passed to
`Nivat.Colle41.lemma41_of_sweep` — was false independently: it constrains `R` not at all
while asserting a nonempty `K ⊆ R`, so `R = ∅` refutes it (`claim43_hsweep_is_false`, §11),
without going through `exists_sweepData` at all.  Had it been passed to `lemma41_of_sweep`,
it would have imported a falsehood into Lemma 4.1.

§1–§10 are unaffected by the withdrawal: they consume `SweepData` as a hypothesis, and §10.2
shows that hypothesis is satisfiable.

## Correction to the previous version of this file

The previous version stated

    line_closure_of_period … (hagree : ∀ j : ℕ, j < c.natAbs → z₀ + (j : ℤ) • u ∈ R → …)
        : ∀ k : ℤ, z₀ + k • u ∈ R → x (z₀ + k • u) = y (z₀ + k • u)

which is **false** — an `ℕ`-indexed window cannot control a `ℤ`-indexed conclusion, and
the `∈ R` guard makes the hypothesis vacuous on the backward ray.  A kernel-checked
refutation is in `Nivat/External/Colle/Claim43Refutation.lean`
(`line_closure_of_period_is_false`).  That statement is **deleted** here and replaced by
the correct forward-ray form `ray_closure_of_period` (§6).  That file's diagnosis is
confirmed: Colle's sweep runs along a direction pointing *into* the region, so `ℕ` is the
right index type.

No `axiom`, `native_decide` or `@[implemented_by]` is introduced, and since the 2026-09-16
withdrawal **this file contains no `sorry`**.  It did not get there by proof: the one `sorry`
it had was closing a statement that §11 refutes, so the statement was withdrawn rather than
discharged.  See §7.
-/

namespace Nivat.Colle43

open Nivat Nivat.Colle Nivat.Colle41

/-! ## §1. Shift-invariance and generation propagation -/

/-- The orbit closure is closed under translation. -/
theorem shift_orbitClosure {A : Type*} {η : Config A} {x : Config A} (u : ℤ × ℤ)
    (hx : x ∈ orbitClosure η) : T u x ∈ orbitClosure η :=
  T_mem_of_mem_orbitClosure hx u

/-- Generation property is preserved under translation. -/
theorem generatesAt_shift {A : Type*} {ξ : Config A} {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    (hgen : GeneratesAt ξ S a) (v : ℤ × ℤ) :
    GeneratesAt ξ (S.map (addLeftEmbedding v)) (a + v) := by
  obtain ⟨ha, hgen_core⟩ := hgen
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_map]
    refine ⟨a, ha, ?_⟩
    simp only [addLeftEmbedding_apply, add_comm]
  · intro x hx y hy hagree
    have hx_shift : T v x ∈ orbitClosure ξ := shift_orbitClosure v hx
    have hy_shift : T v y ∈ orbitClosure ξ := shift_orbitClosure v hy
    have hagree_shift : ∀ z ∈ S.erase a, T v x z = T v y z := by
      intro z hz
      have hzv_mem : v + z ∈ S.map (addLeftEmbedding v) := by
        rw [Finset.mem_map]
        exact ⟨z, Finset.mem_erase.mp hz |>.2, addLeftEmbedding_apply v z⟩
      have hzv_ne_av : v + z ≠ v + a := by
        intro hcontra
        exact Finset.mem_erase.mp hz |>.1 (add_left_cancel hcontra)
      have hzv_erase : z + v ∈ (S.map (addLeftEmbedding v)).erase (a + v) := by
        rw [Finset.mem_erase]
        refine ⟨?_, ?_⟩
        · rw [add_comm z v, add_comm a v]
          exact hzv_ne_av
        · rw [add_comm z v]
          exact hzv_mem
      have heq := hagree (z + v) hzv_erase
      simp only [T_apply]
      convert heq using 1
    have key := hgen_core (T v x) hx_shift (T v y) hy_shift hagree_shift
    simp only [T_apply] at key
    convert key using 1

/-! ## §2. Betweenness in a lattice-convex region

The only convex-geometry fact the sweep needs: along a fixed lattice direction, a
lattice-convex region contains every lattice point between two of its points. -/

/-- If `z₀ + a•u` and `z₀ + b•u` lie in a lattice-convex region `R` and `a ≤ m ≤ b`,
then `z₀ + m•u ∈ R`. -/
theorem between_mem {R : Set (ℤ × ℤ)} (hconv : IsLatticeConvexRegion R)
    {z₀ u : ℤ × ℤ} {a b m : ℤ}
    (ha : z₀ + a • u ∈ R) (hb : z₀ + b • u ∈ R) (hm1 : a ≤ m) (hm2 : m ≤ b) :
    z₀ + m • u ∈ R := by
  obtain ⟨C, hCconv, _, hReq⟩ := hconv
  rw [hReq] at ha hb ⊢
  simp only [Set.mem_preimage] at ha hb ⊢
  rcases eq_or_lt_of_le (hm1.trans hm2) with hab | hab
  · have : m = a := by omega
    rw [this]; exact ha
  · set t : ℝ := ((m : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)) with ht
    have hba : (0 : ℝ) < (b : ℝ) - (a : ℝ) := by
      have : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
      linarith
    have ht0 : 0 ≤ t := by
      apply div_nonneg _ (le_of_lt hba)
      have : (a : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      linarith
    have ht1 : t ≤ 1 := by
      rw [ht, div_le_one hba]
      have : (m : ℝ) ≤ (b : ℝ) := by exact_mod_cast hm2
      linarith
    have key : toReal (z₀ + m • u) =
        (1 - t) • toReal (z₀ + a • u) + t • toReal (z₀ + b • u) := by
      have hne : ((b : ℝ) - (a : ℝ)) ≠ 0 := ne_of_gt hba
      apply Prod.ext <;>
        simp only [toReal, Prod.fst_add, Prod.snd_add, Prod.smul_def, smul_eq_mul,
          Prod.mk_add_mk] <;>
        push_cast <;>
        rw [ht] <;> field_simp <;> ring
    rw [key]
    exact hCconv ha hb (by linarith) ht0 (by ring)

/-- **The engine.**  A lattice-convex region containing `a` and `b` contains any `c` with
`a + b = c + c`: `toReal c` is the midpoint of `toReal a` and `toReal b`.

This is the degenerate two-point case of `between_mem` (the `t = 1/2` instance), stated
without the ray parametrisation.  It is what makes lattice convexity *bite* in the
refutations of the naive sweep encodings (`tmp/L3_row0_and_swept_repair.lean`). -/
theorem latticeConvexRegion_midpoint {K : Set (ℤ × ℤ)} (hK : IsLatticeConvexRegion K)
    {a b c : ℤ × ℤ} (ha : a ∈ K) (hb : b ∈ K) (habc : a + b = c + c) : c ∈ K := by
  obtain ⟨C, hconv, -, hKeq⟩ := hK
  rw [hKeq] at ha hb ⊢
  have hmem := hconv ha hb (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  have e : (1 / 2 : ℝ) • toReal a + (1 / 2 : ℝ) • toReal b = toReal c := by
    have h2 : toReal a + toReal b = toReal c + toReal c := by
      rw [← toReal_add, ← toReal_add, habc]
    have h3 : (1 / 2 : ℝ) • (toReal a + toReal b)
        = (1 / 2 : ℝ) • (toReal c + toReal c) := by rw [h2]
    rw [smul_add, smul_add] at h3
    rw [h3]
    module
  rw [e] at hmem
  exact hmem

/-! ## §3. The generating-window sweep along one line

This is the inner induction of Claim 4.3: *"since `𝒮` is an `η`-generating set, from
(4.4) we can, by induction, enlarge the set where `x` and `T^{(s−r)h'} x` coincide"*. -/

/-- **One sweep step.**  If the punctured generating window `𝒮 \ {a}`, translated by `v`,
lands inside a set `D` on which `x` and `y` already agree, then `x` and `y` agree at the
new point `a + v`.

This is exactly the `η`-generating property applied to the translated configurations
`T^v x` and `T^v y`, both of which stay in the orbit closure. -/
theorem agree_at_of_generatesAt {A : Type*} {η x y : Config A}
    (hx : x ∈ orbitClosure η) (hy : y ∈ orbitClosure η)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : GeneratesAt η S a)
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, x z = y z)
    (v : ℤ × ℤ) (hwin : ∀ z ∈ S.erase a, z + v ∈ D) :
    x (a + v) = y (a + v) := by
  refine hgen.2 (T v x) (T_mem_of_mem_orbitClosure hx v)
    (T v y) (T_mem_of_mem_orbitClosure hy v) ?_
  intro z hz
  show x (z + v) = y (z + v)
  exact hD _ (hwin z hz)

/-- **The sweep engine (inner induction).**  `f 0, f 1, …` enumerates the lattice points
to be conquered in order.  If at every stage `j` the punctured generating window,
translated so that `a` sits at `f j`, lands inside the seed `D` together with the
*strictly earlier* stages `{f i : i < j}`, then `x` and `y` agree at every `f j`.

Note that the window is allowed to reach into points conquered earlier in the *same*
sweep — that is precisely what makes the induction non-trivial, and it is why the proof
is by strong induction rather than by a single application of `agree_at_of_generatesAt`. -/
theorem sweep_induction {A : Type*} {η x y : Config A}
    (hx : x ∈ orbitClosure η) (hy : y ∈ orbitClosure η)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : GeneratesAt η S a)
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, x z = y z)
    (f : ℕ → ℤ × ℤ)
    (hwin : ∀ j : ℕ, ∀ z ∈ S.erase a, z + (f j - a) ∈ D ∪ (f '' {i | i < j})) :
    ∀ j : ℕ, x (f j) = y (f j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    have key : x (a + (f j - a)) = y (a + (f j - a)) := by
      refine agree_at_of_generatesAt hx hy hgen
        (D := D ∪ (f '' {i | i < j})) ?_ (f j - a) (hwin j)
      rintro z (hzD | ⟨i, hi, rfl⟩)
      · exact hD z hzD
      · exact ih i hi
    have e : a + (f j - a) = f j := by abel
    rwa [e] at key

/-- `sweep_induction` in the concrete arithmetic-progression form used along a lattice
line: the points conquered are `g₀, g₀ + w, g₀ + 2w, …`. -/
theorem line_sweep_along {A : Type*} {η x y : Config A}
    (hx : x ∈ orbitClosure η) (hy : y ∈ orbitClosure η)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : GeneratesAt η S a)
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, x z = y z)
    (g₀ w : ℤ × ℤ)
    (hwin : ∀ j : ℕ, ∀ z ∈ S.erase a,
      z + (g₀ + (j : ℤ) • w - a) ∈ D ∨
        ∃ i : ℕ, i < j ∧ z + (g₀ + (j : ℤ) • w - a) = g₀ + (i : ℤ) • w) :
    ∀ j : ℕ, x (g₀ + (j : ℤ) • w) = y (g₀ + (j : ℤ) • w) := by
  refine sweep_induction hx hy hgen hD (fun j => g₀ + (j : ℤ) • w) ?_
  intro j z hz
  rcases hwin j z hz with h | ⟨i, hi, he⟩
  · exact Or.inl h
  · exact Or.inr ⟨i, hi, he.symm⟩

/-! ## §4. The outer induction over the successive lines `ℓ₀, ℓ₁, …, ℓ_M`

Colle: *"The same idea applied to the lines `ℓ_i` for `i = 2, …, M`, where
`ℓ_M = ℓ_{Q'}`, allows us to conclude …"*.  Formally this is a second strong induction,
nested outside the first: when conquering line `ℓ_i` the window may reach into the seed,
into **all** of the lines `ℓ_{i'}` with `i' < i`, and into the earlier points of `ℓ_i`
itself. -/

/-- **The sweep engine (outer induction).**  `enum i j` is the `j`-th point conquered on
line `ℓ_i`. -/
theorem multi_line_sweep {A : Type*} {η x y : Config A}
    (hx : x ∈ orbitClosure η) (hy : y ∈ orbitClosure η)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : GeneratesAt η S a)
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, x z = y z)
    (enum : ℕ → ℕ → ℤ × ℤ)
    (hwin : ∀ i j : ℕ, ∀ z ∈ S.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j})) :
    ∀ i j : ℕ, x (enum i j) = y (enum i j) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ihI =>
    have hDprev_ag : ∀ z ∈ D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')),
        x z = y z := by
      rintro z (hzD | hzU)
      · exact hD z hzD
      · simp only [Set.mem_iUnion, Set.mem_range] at hzU
        obtain ⟨i', hi', j', rfl⟩ := hzU
        exact ihI i' hi' j'
    exact sweep_induction hx hy hgen hDprev_ag (enum i) (fun j => hwin i j)

/-! ## §5. The seed (4.4) and the return to `PeriodOn` -/

/-- The half-strip over the finite base `B` in the direction `u'`, from parameter `t₁` on.
This is Colle's `H_Q = {g + t v_{ℓ'} : g ∈ Q \ ℓ'_Q, t ≥ τ + p'}`, with `B` playing the
role of `Q \ ℓ'_Q` and `t₁` of `τ + p'`. -/
def halfStripFrom (B : Finset (ℤ × ℤ)) (u' : ℤ × ℤ) (t₁ : ℤ) : Set (ℤ × ℤ) :=
  {z | ∃ g ∈ B, ∃ t : ℤ, t₁ ≤ t ∧ z = g + t • u'}

theorem mem_halfStripFrom {B : Finset (ℤ × ℤ)} {u' : ℤ × ℤ} {t₁ : ℤ} {g : ℤ × ℤ}
    (hg : g ∈ B) {t : ℤ} (ht : t₁ ≤ t) : g + t • u' ∈ halfStripFrom B u' t₁ :=
  ⟨g, hg, t, ht, rfl⟩

/-- **The seed of the sweep, i.e. equation (4.4).**  A single `q`-step periodicity of `x`
on the half-strip iterates to agreement of `x` with its `(n q) v_{ℓ'}`-translate on the
whole half-strip, for every `n : ℕ`.

The hypothesis `hqper` is *literally* the antecedent of the `hsweep` hypothesis of
`Nivat.Colle41.lemma41_of_sweep`, with `t₁ := τ + p`. -/
theorem agree_T_on_halfStripFrom {A : Type*} {x : Config A}
    {B : Finset (ℤ × ℤ)} {u' : ℤ × ℤ} {t₁ : ℤ} {q : ℕ}
    (hqper : ∀ g ∈ B, ∀ t : ℤ, t₁ ≤ t → x (g + (t + (q : ℤ)) • u') = x (g + t • u'))
    (n : ℕ) :
    ∀ z ∈ halfStripFrom B u' t₁, x z = T (((n * q : ℕ) : ℤ) • u') x z := by
  rintro z ⟨g, hg, t, ht, rfl⟩
  show x (g + t • u') = x (g + t • u' + ((n * q : ℕ) : ℤ) • u')
  have key : ∀ m : ℕ, x (g + ((t + (m : ℤ) * (q : ℤ)) • u')) = x (g + t • u') := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hle : t₁ ≤ t + (m : ℤ) * (q : ℤ) := by
        have : (0 : ℤ) ≤ (m : ℤ) * (q : ℤ) := by positivity
        omega
      have e : t + ((m + 1 : ℕ) : ℤ) * (q : ℤ)
          = (t + (m : ℤ) * (q : ℤ)) + (q : ℤ) := by push_cast; ring
      rw [e, hqper g hg _ hle, ih]
  have e2 : g + t • u' + ((n * q : ℕ) : ℤ) • u'
      = g + (t + (n : ℤ) * (q : ℤ)) • u' := by
    push_cast
    rw [add_smul]
    abel
  rw [e2, key n]

/-- Agreement of `x` with its own `h`-translate on `U` is `PeriodOn x U h`.  (The
converse needs the overlap guard of Definition 2.11, so this direction is the useful
one: `PeriodOn` is the *weaker* statement.) -/
theorem periodOn_of_agree_T {A : Type*} {x : Config A} {U : Set (ℤ × ℤ)} {h : ℤ × ℤ}
    (hag : ∀ z ∈ U, x z = T h x z) : PeriodOn x U h := fun z hz _ => (hag z hz).symm

/-- **Claim 4.3, assembled.**  If the sweep, started from a seed `D` on which `x` already
agrees with its `h'`-translate, conquers enough points to cover `K`, then `x|K` is
`h'`-periodic. -/
theorem claim43_periodOn_of_sweep {A : Type*} {η x : Config A}
    (hx : x ∈ orbitClosure η)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : GeneratesAt η S a)
    (h' : ℤ × ℤ)
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, x z = T h' x z)
    (enum : ℕ → ℕ → ℤ × ℤ)
    (hwin : ∀ i j : ℕ, ∀ z ∈ S.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪ (enum i '' {j' | j' < j}))
    {K : Set (ℤ × ℤ)} (hK : K ⊆ D ∪ (⋃ i, Set.range (enum i))) :
    PeriodOn x K h' := by
  have hcov : ∀ i j : ℕ, x (enum i j) = T h' x (enum i j) :=
    multi_line_sweep hx (T_mem_of_mem_orbitClosure hx h') hgen hD enum hwin
  refine periodOn_of_agree_T ?_
  intro z hz
  rcases hK hz with hzD | hzU
  · exact hD z hzD
  · simp only [Set.mem_iUnion, Set.mem_range] at hzU
    obtain ⟨i, j, rfl⟩ := hzU
    exact hcov i j

/-! ## §6. Forward-ray closure

Replacement for the refuted `line_closure_of_period` (see the module docstring and
`Nivat/External/Colle/Claim43Refutation.lean`).  The index type of the conclusion is `ℕ`,
matching the `ℕ`-indexed agreement window, and the region hypothesis is a *ray*
hypothesis, which is what forbids the backward escape that killed the old statement. -/

/-- If `x` and `y` are both `c·u`-periodic on `U`, `U` contains the whole forward ray
`z₀, z₀ + u, z₀ + 2u, …`, and `x = y` on the first `c` points of that ray, then `x = y`
on the whole ray. -/
theorem ray_closure_of_period {A : Type*} {x y : Config A} {U : Set (ℤ × ℤ)}
    {u : ℤ × ℤ} {c : ℕ} (hc : 0 < c)
    (hxper : PeriodOn x U ((c : ℤ) • u)) (hyper : PeriodOn y U ((c : ℤ) • u))
    {z₀ : ℤ × ℤ} (hray : ∀ k : ℕ, z₀ + (k : ℤ) • u ∈ U)
    (hagree : ∀ j : ℕ, j < c → x (z₀ + (j : ℤ) • u) = y (z₀ + (j : ℤ) • u)) :
    ∀ k : ℕ, x (z₀ + (k : ℤ) • u) = y (z₀ + (k : ℤ) • u) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < c
    · exact hagree k hk
    · have hck : c ≤ k := Nat.le_of_not_lt hk
      have hmk : k - c < k := by omega
      have hsplit : z₀ + (k : ℤ) • u = (z₀ + ((k - c : ℕ) : ℤ) • u) + (c : ℤ) • u := by
        have : (k : ℤ) = ((k - c : ℕ) : ℤ) + (c : ℤ) := by omega
        rw [this, add_smul]; abel
      rw [hsplit, hxper _ (hray (k - c)) (by rw [← hsplit]; exact hray k),
        hyper _ (hray (k - c)) (by rw [← hsplit]; exact hray k)]
      exact ih (k - c) hmk

/-! ## §7. Discharging `hsweep`

`SweepData` bundles exactly the geometric input that Claim 4.3 consumes.  Given it,
`hsweep_of_sweepData` produces the `hsweep` hypothesis of
`Nivat.Colle41.lemma41_of_sweep` verbatim, with no `sorry`. -/

/-- **The geometric data skeleton consumed by Colle's sweep, for a fixed step `q`.**

* `K` with `subset_R`, `isRegion`, `nonempty` — the `(ℓ,ℓ')`-region
  `𝒦 = ℋ(ℓ_{Q'}) ∩ ℛ` of the conclusion;
* `t₀` with `t₀_pos` — the pigeonhole gap `0 < t'₀ ≤ P_η(𝒯) + 1`;
* `S`, `a`, `generates` — the `η`-generating window and its distinguished point;
* `enum` with `window` — the enumeration of the successive lines `ℓ₀, ℓ₁, …, ℓ_M` and the
  assertion that each new point's window falls into the already-conquered set;
* `covers` — the assertion that the seed together with the enumerated lines exhausts `K`.

### Why `covers` is a field and not a theorem

A previous version of this file deleted `covers` from the structure, on the grounds that
"the coverage property is precisely the geometric core of Claim 4.3, so assuming it as part
of the input data concealed the gap", and replaced it by a standalone theorem
`sweepData_covers` carrying a `sorry`.  **That refactoring was wrong, and the statement it
left behind is false.**  §10 below contains a kernel-checked refutation
(`sweep_covers_not_derivable`): nothing in the remaining fields relates `enum` to `K` at
all, so `enum` may enumerate a single point while `K` is all of `ℤ²`, with `window`
satisfied by a genuinely two-point generating window and a genuine half-strip seed.  §10
also shows (`sweep_covers_failure_gives_False`) that granting the deleted statement for
that data yields `PeriodOn rowConfig ℤ² (0,1)`, which is false — i.e. the `sorry` was not
standing in for an unproved truth, it was standing in for a falsehood, which made
`hsweep_of_sweepData` and `claim43_hsweep` false theorems.

The circularity worry that motivated the deletion does not apply: `covers` is a statement
about *sets* and never mentions the configuration `x`, so it cannot be the periodicity
conclusion in disguise.  `sweepData_config_indep` (§9) is the machine-checked witness of
this: the whole of `SweepData`, `covers` included, transports verbatim from any `x` to any
other.  In Colle's proof, coverage is likewise part of the *construction* of the lines —
the lines `ℓ₀, ℓ₁ := ℓ₀^{(−)}, …, ℓ_M = ℓ_{Q'}` exhaust the half strip
`ℋ(ℓ_{Q'}) ∩ ℛ ∩ ℋ(−ℓ_{𝒯+rh'})` by construction — not a consequence of the sweep.

The real debt is therefore, and has always been, `exists_sweepData`: producing data that
satisfies all of these fields simultaneously.  `goodSweepData` (§10) shows the bundle is
satisfiable in a non-degenerate instance, so the debt is a genuine construction problem and
not a hidden contradiction. -/
structure SweepData {A : Type*} (η x : Config A) (u u' : ℤ × ℤ)
    (R : Set (ℤ × ℤ)) (B : Finset (ℤ × ℤ)) (t₁ : ℤ) (q : ℕ) where
  /-- The `(ℓ,ℓ')`-region of the conclusion. -/
  K : Set (ℤ × ℤ)
  subset_R : K ⊆ R
  isRegion : IsRegion K u u'
  nonempty : K.Nonempty
  /-- The pigeonhole gap `t'₀`. -/
  t₀ : ℕ
  t₀_pos : 0 < t₀
  /-- The `η`-generating window `𝒮` and its distinguished point `a`. -/
  S : Finset (ℤ × ℤ)
  a : ℤ × ℤ
  generates : GeneratesAt η S a
  /-- `enum i j` is the `j`-th point conquered on the line `ℓ_i`. -/
  enum : ℕ → ℕ → ℤ × ℤ
  window : ∀ i j : ℕ, ∀ z ∈ S.erase a,
    z + (enum i j - a) ∈
      halfStripFrom B u' t₁ ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i'))
        ∪ (enum i '' {j' | j' < j})
  /-- The seed half-strip together with the enumerated lines exhausts `K`.  Purely
  geometric: it does not mention `x`.  See the structure docstring and §10. -/
  covers : K ⊆ halfStripFrom B u' t₁ ∪ (⋃ i, Set.range (enum i))

/-- **`SweepData` with the h-periodicity constraint from Collé's proof.**

Extends `SweepData` with the period field that Collé's Claim 4.3 proof opens with
(`scratch/b3_colle2.txt:684`, verbatim): *"Indeed, let `h ∈ ℤ²` be a period for `x|ℛ`
parallel to `ℓ`."*  This is the condition that allows the induction to conquer only a
finite window on each line `ℓ_i` rather than the entire line — the rest is filled by
h-periodicity (`b3_colle2.txt:698`).

The bridge `toSweepData` forgets the period, so existing consumers of `SweepData` compile
unchanged (CLAUDE.md 「定义修法：加强，不替换」). -/
structure SweepDataWithPeriod {A : Type*} (η x : Config A) (u u' : ℤ × ℤ)
    (R : Set (ℤ × ℤ)) (B : Finset (ℤ × ℤ)) (t₁ : ℤ) (q : ℕ) extends
    SweepData η x u u' R B t₁ q where
  /-- The period `h` for `x|ℛ`, parallel to `ℓ` (`b3_colle2.txt:684`). -/
  h : ℤ × ℤ
  h_period : h ∈ Per x
  h_periodOn_R : ∀ z ∈ R, x (z + h) = x z
  /-- `h` is parallel to `u` (which plays the role of `ℓ` in the paper). -/
  h_parallel_u : ∃ t : ℤ, h = t • u

/-- **The forgetful bridge: `SweepDataWithPeriod` satisfies `SweepData`.**

Every existing consumer of `SweepData` works unchanged via this projection. -/
theorem SweepDataWithPeriod.toSweepData_eq {A : Type*} {η x : Config A} {u u' : ℤ × ℤ}
    {R : Set (ℤ × ℤ)} {B : Finset (ℤ × ℤ)} {t₁ : ℤ} {q : ℕ}
    (d : SweepDataWithPeriod η x u u' R B t₁ q) :
    d.toSweepData = ⟨d.K, d.subset_R, d.isRegion, d.nonempty, d.t₀, d.t₀_pos,
      d.S, d.a, d.generates, d.enum, d.window, d.covers⟩ :=
  rfl

/-- **The coverage property: the sweep enumeration reaches all of `K`.**

Statement unchanged from the previous version of this file; only its *provenance* has
changed.  It is **not** derivable from the other fields of `SweepData` — see
`sweep_covers_not_derivable` in §10 for a kernel-checked counterexample — so it is now
supplied by the `covers` field rather than by a `sorry`.

This theorem therefore records no mathematical progress: the content it used to hide has
moved, intact, into `exists_sweepData`, which must now also construct `covers`. -/
theorem sweepData_covers {A : Type*} {η x : Config A} {u u' : ℤ × ℤ}
    {R : Set (ℤ × ℤ)} {B : Finset (ℤ × ℤ)} {t₁ : ℤ} {q : ℕ}
    (d : SweepData η x u u' R B t₁ q) :
    d.K ⊆ halfStripFrom B u' t₁ ∪ (⋃ i, Set.range (d.enum i)) :=
  d.covers

/-- **`hsweep` from `SweepData`.**  This is Claim 4.3 together with the final paragraph of
Colle's proof of Lemma 4.1, in exactly the shape required by
`Nivat.Colle41.lemma41_of_sweep`.

Now depends on `sweepData_covers` to supply the coverage property; since `sweepData_covers`
is the `covers` field of the data (see §10 for why it cannot be a theorem), all the
periodicity in the conclusion is still manufactured by the induction of §3–§4 out of
`hqper` — `SweepData` never mentions `x` (`sweepData_config_indep`). -/
theorem hsweep_of_sweepData {A : Type*} {η x : Config A} (hx : x ∈ orbitClosure η)
    {u u' : ℤ × ℤ} {R : Set (ℤ × ℤ)} {B : Finset (ℤ × ℤ)} {t₁ : ℤ} {q : ℕ}
    (d : SweepData η x u u' R B t₁ q)
    (hqper : ∀ g ∈ B, ∀ t : ℤ, t₁ ≤ t → x (g + (t + (q : ℤ)) • u') = x (g + t • u')) :
    ∃ K : Set (ℤ × ℤ), K ⊆ R ∧ IsRegion K u u' ∧ K.Nonempty ∧
      ∃ t₀ : ℕ, 0 < t₀ ∧ PeriodOn x K (((t₀ * q : ℕ) : ℤ) • u') := by
  refine ⟨d.K, d.subset_R, d.isRegion, d.nonempty, d.t₀, d.t₀_pos, ?_⟩
  exact claim43_periodOn_of_sweep hx d.generates (((d.t₀ * q : ℕ) : ℤ) • u')
    (agree_T_on_halfStripFrom hqper d.t₀) d.enum d.window (sweepData_covers d)

/-! ## §7. Withdrawn: `exists_sweepData` and `claim43_hsweep` (2026-09-16)

Both statements were removed on 2026-09-16.  They were not unproved; they were **false**,
and §11 proves it in the kernel:

* `exists_sweepData_is_false` — `exists_sweepData` quantifies over every `η` without
  assuming `η` has a generating window, while `SweepData` demands one in its `generates`
  field.  The delta configuration (`deltaConfig`, §11) satisfies every hypothesis and admits
  no `GeneratesAt` at all (`no_generatesAt_delta`).
* `claim43_hsweep_is_false` — it places no constraint on `R` while asserting a nonempty
  `K ⊆ R`, so `R = ∅` refutes it outright, independently of `exists_sweepData`.

The `sorry` that closed `exists_sweepData` was therefore standing in for a falsehood, and
`claim43_hsweep` would have exported that falsehood to `Nivat.Colle41.lemma41_of_sweep`.
Neither had a single term-level consumer anywhere in `Nivat/` (checked 2026-09-16;
`Lemma45.lean:46` names this module only in a "will import once F1/F2 complete" note, and
`Lemma45.lean:4-6` does not import it).  The signatures are not silently repaired here: a
repair needs an added hypothesis, and choosing it is a mathematical decision, not
bookkeeping.  Be warned that the obvious candidate (`∃ S a, GeneratesAt η S a`) is
**believed to be insufficient** — that is a hand derivation, not a kernel result, and the
first person to attempt the repair should refute or confirm it before building on it.

**Nothing was lost by the withdrawal.**  The working, conditional form is proved and
`sorry`-free and is what the rest of the development should consume:

    hsweep_of_sweepData (§7 above) : SweepData η x u u' R B t₁ q → (periodicity conclusion)

and §10.2 exhibits `goodSweepData`, a `SweepData` satisfying **every** field including
`covers`, with `goodSweepData_hsweep` deriving the full conclusion from it.  So the sweep
induction of Claim 4.3 is formalised and fires; what is missing is the *construction* that
produces a `SweepData` in general.  Do not repeat the summary "Claim 4.3 is unformalised" —
it is the existence half that is open.

### What a correctly stated `exists_sweepData` would still need

Retained verbatim from the withdrawn docstring, because it remains an accurate account of
the missing mathematics.  Note that the old docstring's claim that item 2 is "the binding
constraint" was written before the statement was known to be false; the binding constraint
on the *stated* theorem was the missing generating-window hypothesis.  In Colle's order:

1. **The `E(𝒮)`-enveloped set `𝒯 ⊂ ℛ` satisfying (4.3)** (paper, paragraph before
   Claim 4.3).  Colle: *"suppose `𝒯 ⊂ ℛ` is an `E(𝒮)`-enveloped set large enough so
   that, for any integers `0 ≤ r < s`, (4.3) holds"*, justified by *"Of course this is
   possible because by assumption `x|ℛ` is periodic with period parallel to `ℓ`"*.  The
   quantifier "large enough" is never made explicit; making it explicit is a genuine
   piece of missing mathematics, not bookkeeping.  `Nivat.LE2.Enveloped` (Definition 3.2)
   is available in `Nivat/External/Colle/LatticeEdges.lean`, but no existence theorem for
   an enveloped set with property (4.3) is.

2. **The `(ℓ,ℓ')`-region `𝒦 = ℋ(ℓ_{Q'}) ∩ ℛ`, with its two semi-infinite edges.**  This
   is the `K`, `isRegion`, `nonempty` part of `SweepData`.

   *Attribution corrected 2026-09-17.*  This item previously read "it is the output of
   Colle's Claim 4.6 / Claim 4.11 region construction … nothing available produces an
   `IsRegion` witness inside a given `ℛ`".  That was wrong, and self-contradictory with
   the formula in this item's own heading.  `𝒦` is the output of **Lemma 4.1**, whose
   proof ends (`b3_colle2.txt:700`) with *"Claim 4.3 implies that `x|ℋ(ℓ_{Q'}) ∩ ℛ` is
   periodic of period `t'₀h'`"* — that display **is** the construction of `𝒦`.  Claim 4.6
   and Claim 4.11 supply the *input* region `ℛ`, not `𝒦`: `b3_colle2.txt:860` reads
   "Due to Claim 4.7 **and Lemma 4.1**, there exists … `𝒦 ⊂ 𝓡^N_I`" and `:904` reads
   "Due to Claim 4.11 **and Lemma 4.1**, there exists … `𝒦 ⊂ Â_∞^{(ε)}`".  The arrows
   therefore run one way (4.6/4.11 → ℛ → Lemma 4.1 → 𝒦) and there is no circularity.

   Consequence: the obligation here is **not** the existence statement "some `IsRegion`
   witness exists inside an arbitrary `ℛ`", but the geometric statement "intersecting a
   region with the half plane `ℋ(ℓ_{Q'})` again yields a region, with the second edge
   direction replaced".  A statement-level probe for that lemma is in flight; until it
   lands, do not schedule this item by any hour estimate.

3. **The line recursion `ℓ_{i+1} := ℓ_i^{(−)}` and the window condition.**  The `enum` and
   `window` fields.  `Nivat.LE2.outerLine` formalises `ℓ^{(−)}` and `Nivat.LE2.face` /
   `Nivat.LE2.E` the edge vocabulary, so the *statement* is expressible; what is missing is
   the cardinality count that makes the induction go through, namely Colle's *"the convex
   set `ℓ₁ ∩ (H_Q − ι h)` has at least `|𝒮 ∩ ℓ_𝒮| − 1` elements"*.  That count needs
   `−ℓ, ℓ ∈ nexpd(η)` (to know via Lemma 2.3 that `𝒮` has an edge parallel to `ℓ` at all,
   so that `|𝒮 ∩ ℓ_𝒮| ≥ 2`), the convexity of `Q`, and the `ι`-independence recorded in
   (4.4).  None of those are assembled here.

4. **The coverage of `𝒦` by the lines** — the `covers` field.  In the paper this is not a
   separate assertion: the lines `ℓ₀, ℓ₁ := ℓ₀^{(−)}, …, ℓ_M = ℓ_{Q'}` are *defined* by the
   `ℓ^{(−)}` recursion of Notation 3.3, which steps one lattice line at a time across the
   strip, so by construction their union is the whole half strip
   `ℋ(ℓ_{Q'}) ∩ ℛ ∩ ℋ(−ℓ_{𝒯+rh'})`.  Formalising that needs the `outerLine` recursion
   together with the halting index `M` — i.e. items 2 and 3 above.  A previous version of
   this file tried to make coverage a *theorem* about an enumeration otherwise unconstrained
   by `𝒦`; §10 refutes that.
-/

/-! ## §8. Pigeonhole

Colle's *"there exist `0 < t'₀ ≤ P_η(𝒯) + 1` and infinitely many integers `r > 0` so that
(4.3) holds for `r` and `s = r + t'₀`"*. -/

/-- **Bounded repeat pigeonhole lemma.**  For any sequence `f : ℕ → A` into a finite type
there is a positive gap `t₀ ≤ card A + 1` realised arbitrarily late. -/
theorem exists_bounded_repeat {A : Type*} [Finite A] (f : ℕ → A) :
    ∃ t₀ : ℕ, 0 < t₀ ∧ (let _ : Fintype A := Fintype.ofFinite A; t₀ ≤ Fintype.card A + 1) ∧
      ∀ N : ℕ, ∃ r ≥ N, ∃ s, r < s ∧ s = r + t₀ ∧ f r = f s := by
  classical
  let _ : Fintype A := Fintype.ofFinite A
  set n := Fintype.card A
  have h_exists_gap : ∀ k : ℕ, ∃ t : ℕ, 1 ≤ t ∧ t ≤ n + 1 ∧
      ∃ r ≥ k, ∃ s, s = r + t ∧ f r = f s := by
    intro k
    let g : Fin (n + 1) → A := fun i => f (k + i.val)
    have card_lt : Fintype.card A < Fintype.card (Fin (n + 1)) := by
      simp [Fintype.card_fin]
      omega
    obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt g card_lt
    by_cases hlt : i.val < j.val
    · use j.val - i.val
      refine ⟨by omega, by omega, k + i.val, by omega, k + j.val, ?_, hfij⟩
      omega
    · push Not at hlt
      have : j.val < i.val := by
        by_contra h
        push Not at h
        have : i.val = j.val := Nat.le_antisymm h hlt
        have : i = j := Fin.ext this
        exact hij this
      use i.val - j.val
      refine ⟨by omega, by omega, k + j.val, by omega, k + i.val, ?_, hfij.symm⟩
      omega
  by_contra h_contra
  push Not at h_contra
  have h_finite_each : ∀ t : ℕ, 1 ≤ t → t ≤ n + 1 →
      ∃ K : ℕ, ∀ r ≥ K, ∀ s, s = r + t → f r ≠ f s := by
    intro t ht1 htn
    obtain ⟨K, hK⟩ := h_contra t (by omega) htn
    use K
    intro r hr s hs
    by_contra heq
    specialize hK r hr s (by omega) hs
    exact hK heq
  choose K hK using h_finite_each
  have hn_pos : 0 < n + 1 := Nat.succ_pos n
  let K_finset := Finset.image (fun (i : Fin (n + 1)) =>
    K (i.val + 1) (Nat.succ_pos i.val) (by omega)) Finset.univ
  have hne : K_finset.Nonempty := by
    simp [K_finset, Finset.Nonempty]
  let K_max := K_finset.max' hne
  obtain ⟨t₀, ht₀_lb, ht₀_ub, r₀, hr₀, s₀, hs₀, hf₀⟩ := h_exists_gap K_max
  have hKt₀_le : K t₀ ht₀_lb ht₀_ub ≤ K_max := by
    apply Finset.le_max'
    simp [K_finset, Finset.mem_image]
    use ⟨t₀ - 1, by omega⟩
    simp
    congr 1
    omega
  have : f r₀ ≠ f s₀ := hK t₀ ht₀_lb ht₀_ub r₀ (Nat.le_trans hKt₀_le hr₀) s₀ hs₀
  exact this hf₀

/-! ## §9. Non-vacuity and non-circularity of the sweep engine

A theorem whose hypotheses cannot be met proves nothing, and one whose hypotheses already
contain its conclusion proves nothing either.  This section rules out both.

`sweepData_config_indep` is the non-circularity check: `SweepData` is *purely geometric* —
none of its fields constrain the configuration `x`, so the data transfers verbatim from
any `x` to any other.  In particular the `covers` and `window` fields cannot be the
periodicity conclusion of Claim 4.3 in disguise; the `PeriodOn` output of
`hsweep_of_sweepData` is genuinely manufactured by the induction in §3–§4 out of the
one-direction seed `hqper`.

`sweep_engine_fires` is the non-vacuity check: the engine is run on a concrete
configuration with a genuinely two-point window (`Swin_erase_nonempty`), deriving
agreement at infinitely many points from a one-point seed. -/

/-- **Non-circularity.**  `SweepData` does not constrain `x` at all.  Hence the
periodicity produced by `hsweep_of_sweepData` is not smuggled in through the geometric
data.  The coverage property `sweepData_covers` is also purely geometric (it depends only
on the region and enumeration structure, not on the configuration `x`), so the full
periodicity conclusion comes exclusively from the induction in §3–§4 applied to the
seed `hqper`. -/
def sweepData_config_indep {A : Type*} {η x : Config A} {u u' : ℤ × ℤ}
    {R : Set (ℤ × ℤ)} {B : Finset (ℤ × ℤ)} {t₁ : ℤ} {q : ℕ}
    (d : SweepData η x u u' R B t₁ q) (x' : Config A) :
    SweepData η x' u u' R B t₁ q where
  K := d.K
  subset_R := d.subset_R
  isRegion := d.isRegion
  nonempty := d.nonempty
  t₀ := d.t₀
  t₀_pos := d.t₀_pos
  S := d.S
  a := d.a
  generates := d.generates
  enum := d.enum
  window := d.window
  covers := d.covers

/-- A simple configuration: the indicator of the row `z.2 = 0`. -/
def rowConfig : Config ℤ := fun z => if z.2 = 0 then 1 else 0

/-- The backward two-point window `{(0,0), (−1,0)}`, distinguished point `(0,0)`. -/
def Swin : Finset (ℤ × ℤ) := {(0, 0), (-1, 0)}

/-- The window is **not** degenerate: the punctured window is non-empty, so
`agree_at_of_generatesAt` really has a hypothesis to discharge. -/
theorem Swin_erase_nonempty : (Swin.erase (0, 0)).Nonempty := by
  refine ⟨(-1, 0), ?_⟩
  rw [Finset.mem_erase]
  refine ⟨by decide, ?_⟩
  simp [Swin]

theorem rowConfig_annihilator :
    let p : LaurentTwo ℤ := AddMonoidAlgebra.single (1, 0) 1 - AddMonoidAlgebra.single (0, 0) 1
    act p rowConfig = 0 := by
  funext z
  simp only [Pi.zero_apply]
  rw [act_sub_left, Pi.sub_apply, act_single, act_single]
  show 1 * rowConfig (z + (1, 0)) - 1 * rowConfig (z + (0, 0)) = 0
  simp only [one_mul, rowConfig]
  have h1 : (z + (1, 0)).2 = z.2 := by simp
  have h2 : (z + (0, 0)).2 = z.2 := by simp
  rw [h1, h2, sub_self]

theorem rowConfig_period : (1, 0) ∈ Per rowConfig := by
  show T (1, 0) rowConfig = rowConfig
  funext z
  simp only [T_apply, rowConfig]
  have : (z + (1, 0)).2 = z.2 := by simp
  rw [this]

/-- `Swin` really is an `η`-generating window for `rowConfig` at `(0,0)`, via the
annihilator `T^{(0,0)} − T^{(−1,0)}`. -/
theorem rowConfig_generatesAt : GeneratesAt rowConfig Swin (0, 0) := by
  classical
  set p : LaurentTwo ℤ := AddMonoidAlgebra.single ((0, 0) : ℤ × ℤ) (1 : ℤ)
    - AddMonoidAlgebra.single ((-1, 0) : ℤ × ℤ) (1 : ℤ) with hp
  have hcoeff : ∀ z : ℤ × ℤ, p.coeff z
      = (if ((0, 0) : ℤ × ℤ) = z then (1 : ℤ) else 0)
        - (if ((-1, 0) : ℤ × ℤ) = z then (1 : ℤ) else 0) := by
    intro z; simp [hp, Finsupp.single_apply]
  have hann : act p rowConfig = 0 := by
    funext z
    rw [hp, act_sub_left, Pi.sub_apply, act_single, act_single]
    show 1 * rowConfig (z + (0, 0)) - 1 * rowConfig (z + (-1, 0)) = 0
    simp only [one_mul, rowConfig]
    have h1 : (z + ((0, 0) : ℤ × ℤ)).2 = z.2 := by simp
    have h2 : (z + ((-1, 0) : ℤ × ℤ)).2 = z.2 := by simp
    rw [h1, h2, sub_self]
  have hsub : supp p ⊆ Swin := by
    intro z hz
    rw [mem_supp, hcoeff] at hz
    by_contra hn
    have h1 : ((0, 0) : ℤ × ℤ) ≠ z := fun h => hn (by rw [← h]; simp [Swin])
    have h2 : ((-1, 0) : ℤ × ℤ) ≠ z := fun h => hn (by rw [← h]; simp [Swin])
    rw [if_neg h1, if_neg h2, sub_zero] at hz
    exact hz rfl
  have hmem : ((0, 0) : ℤ × ℤ) ∈ supp p := by
    rw [mem_supp, hcoeff]; norm_num
  exact generatesAt_of_annihilator hann hsub hmem

/-- **The sweep engine fires.**  From agreement at the *single* seed point `(−1, 0)`,
`line_sweep_along` derives agreement of `rowConfig` and `T^{(3,0)} rowConfig` at *every*
point of the infinite ray `(0,0), (1,0), (2,0), …`.

Each step genuinely uses the generating window: to conquer `(j, 0)` the window reaches
back to `(j − 1, 0)`, which is the point conquered at the previous step (or the seed when
`j = 0`).  So this is a real run of the induction, not a restatement of the conclusion. -/
theorem sweep_engine_fires :
    ∀ j : ℕ, rowConfig ((0, 0) + (j : ℤ) • ((1, 0) : ℤ × ℤ))
      = T (3, 0) rowConfig ((0, 0) + (j : ℤ) • ((1, 0) : ℤ × ℤ)) := by
  have hseed : ∀ z ∈ ({(-1, 0)} : Set (ℤ × ℤ)), rowConfig z = T (3, 0) rowConfig z := by
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    show rowConfig (-1, 0) = rowConfig ((-1, 0) + (3, 0))
    norm_num [rowConfig]
  refine line_sweep_along (η := rowConfig) (self_mem_orbitClosure rowConfig)
    (T_mem_orbitClosure rowConfig (3, 0)) rowConfig_generatesAt hseed (0, 0) (1, 0) ?_
  intro j z hz
  -- the punctured window is exactly `{(-1,0)}`
  have hzeq : z = (-1, 0) := by
    rw [Finset.mem_erase] at hz
    have := hz.2
    simp only [Swin, Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h
    · exact absurd h hz.1
    · exact h
  subst hzeq
  rcases Nat.eq_zero_or_pos j with hj | hj
  · -- `j = 0`: the window lands on the seed
    subst hj
    left
    rw [Set.mem_singleton_iff]
    norm_num
  · -- `j ≥ 1`: the window lands on the point conquered at step `j - 1`
    right
    refine ⟨j - 1, by omega, ?_⟩
    have : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
    rw [this]
    simp only [Prod.smul_def, smul_eq_mul]
    apply Prod.ext <;> simp <;> omega

/-- Non-vacuity: shift-invariance holds for translates of any config. -/
example : T (5, 3) rowConfig ∈ orbitClosure rowConfig :=
  T_mem_orbitClosure rowConfig (5, 3)

/-! ## §10. Why `covers` must be a field: refutation and a satisfying instance

This section discharges the two companion obligations for the `SweepData` structure — an
instance that satisfies it and an instance that fails it — and, more importantly, records
the reason the `covers` field was reinstated.

* §10.1 `sweep_covers_not_derivable`: concrete data satisfying **every** field of
  `SweepData` except `covers`, with a genuinely two-point generating window and a genuine
  half-strip seed, for which the coverage inclusion is false.  So the standalone theorem
  `d.K ⊆ halfStripFrom B u' t₁ ∪ ⋃ i, Set.range (d.enum i)`, quantified over a `SweepData`
  lacking the `covers` field, is not merely unproved — it is refuted.
* §10.1 `sweep_covers_failure_gives_False`: granting the coverage inclusion for that data
  and running §5's `claim43_periodOn_of_sweep` produces `PeriodOn rowConfig ℤ² (0,1)`,
  which is false.  So the deleted field could not be replaced by a `sorry`-ed theorem
  without turning `hsweep_of_sweepData` and `claim43_hsweep` into false theorems.
* §10.2 `goodSweepData`: a full `SweepData`, `covers` included, in which the sweep does
  real work — the region is the quadrant `{(n,m) : n ≥ 0, m ≥ 1}`, the seed is only its
  left edge column, and every other point is conquered from its left neighbour across
  infinitely many lines.  `goodSweepData_periodOn` runs the engine on it and the resulting
  periodicity is true. -/

/-- The punctured window `Swin.erase (0,0)` is exactly `{(-1,0)}`. -/
theorem swin_erase_eq {z : ℤ × ℤ} (hz : z ∈ Swin.erase (0, 0)) : z = (-1, 0) := by
  rw [Finset.mem_erase] at hz
  have := hz.2
  simp only [Swin, Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h | h
  · exact absurd h hz.1
  · exact h

/-! ### §10.1 The coverage inclusion is not a consequence of the other fields -/

/-- Refuting witness: the region is all of `ℤ²`. -/
def refK : Set (ℤ × ℤ) := Set.univ

/-- Refuting witness: the half-strip base is the origin, so the seed is the column
`{(0,t) : t ≥ 1}`. -/
def refB : Finset (ℤ × ℤ) := {(0, 0)}

/-- Refuting witness: the enumeration conquers the single point `(1,1)`, for ever. -/
def refEnum : ℕ → ℕ → ℤ × ℤ := fun _ _ => (1, 1)

theorem mem_refStrip {t : ℤ} (ht : 1 ≤ t) :
    ((0, t) : ℤ × ℤ) ∈ halfStripFrom refB (0, 1) 1 := by
  refine ⟨(0, 0), by simp [refB], t, ht, ?_⟩
  simp

/-- The window condition holds for `refEnum`: the punctured window of `(1,1)` is `(0,1)`,
which sits in the seed half-strip. -/
theorem refWindow : ∀ i j : ℕ, ∀ z ∈ Swin.erase (0, 0),
    z + (refEnum i j - (0, 0)) ∈
      halfStripFrom refB (0, 1) 1 ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (refEnum i'))
        ∪ (refEnum i '' {j' | j' < j}) := by
  intro i j z hz
  rw [swin_erase_eq hz]
  have e : ((-1, 0) : ℤ × ℤ) + (refEnum i j - (0, 0)) = ((0, 1) : ℤ × ℤ) := by
    apply Prod.ext <;> simp [refEnum]
  rw [e]
  exact Or.inl (Or.inl (mem_refStrip le_rfl))

/-- The `q = 1` seed hypothesis of `hsweep_of_sweepData` holds for this data: on the column
`{(0,t) : t ≥ 1}` the row indicator is constantly `0`. -/
theorem refHqper : ∀ g ∈ refB, ∀ t : ℤ, (1 : ℤ) ≤ t →
    rowConfig (g + (t + ((1 : ℕ) : ℤ)) • ((0, 1) : ℤ × ℤ))
      = rowConfig (g + t • ((0, 1) : ℤ × ℤ)) := by
  intro g hg t ht
  have hg' : g = ((0, 0) : ℤ × ℤ) := by simpa [refB] using hg
  subst hg'
  have h1 : ((0, 0) : ℤ × ℤ) + (t + ((1 : ℕ) : ℤ)) • ((0, 1) : ℤ × ℤ) = (0, t + 1) := by
    simp
  have h2 : ((0, 0) : ℤ × ℤ) + t • ((0, 1) : ℤ × ℤ) = (0, t) := by simp
  rw [h1, h2]
  simp only [rowConfig]
  rw [if_neg (by omega), if_neg (by omega)]

/-- **The coverage inclusion is not derivable from the other `SweepData` fields.**

Every field of `SweepData` other than `covers` is satisfied by
`K := refK, S := Swin, a := (0,0), enum := refEnum` over
`η = x = rowConfig, u = (1,0), u' = (0,1), R = ℤ², B = refB, t₁ = 1, q = 1`, the punctured
generating window is non-empty, and yet the coverage inclusion fails. -/
theorem sweep_covers_not_derivable :
    refK ⊆ (Set.univ : Set (ℤ × ℤ)) ∧ IsRegion refK (1, 0) (0, 1) ∧ refK.Nonempty ∧
      GeneratesAt rowConfig Swin (0, 0) ∧ (Swin.erase (0, 0)).Nonempty ∧
      (∀ i j : ℕ, ∀ z ∈ Swin.erase (0, 0),
        z + (refEnum i j - (0, 0)) ∈
          halfStripFrom refB (0, 1) 1 ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (refEnum i'))
            ∪ (refEnum i '' {j' | j' < j})) ∧
      ¬ (refK ⊆ halfStripFrom refB (0, 1) 1 ∪ (⋃ i, Set.range (refEnum i))) := by
  refine ⟨Set.subset_univ _,
    ⟨isLatticeConvexRegion_univ, ⟨0, fun _ => Set.mem_univ _⟩, ⟨0, fun _ => Set.mem_univ _⟩⟩,
    ⟨0, Set.mem_univ _⟩, rowConfig_generatesAt, Swin_erase_nonempty, refWindow, ?_⟩
  intro h
  have hmem : ((5, 7) : ℤ × ℤ) ∈
      halfStripFrom refB ((0, 1) : ℤ × ℤ) 1 ∪ (⋃ i, Set.range (refEnum i)) :=
    h (Set.mem_univ _)
  rcases hmem with hL | hR
  · obtain ⟨g, hg, t, _, hgt⟩ := hL
    have hg' : g = ((0, 0) : ℤ × ℤ) := by simpa [refB] using hg
    subst hg'
    have hfst : ((5 : ℤ), (7 : ℤ)).1 = (((0, 0) : ℤ × ℤ) + t • ((0, 1) : ℤ × ℤ)).1 := by
      rw [← hgt]
    simp at hfst
  · simp only [Set.mem_iUnion, Set.mem_range] at hR
    obtain ⟨i, j, hj⟩ := hR
    rw [show refEnum i j = ((1, 1) : ℤ × ℤ) from rfl] at hj
    exact absurd hj (by decide)

/-- **Granting the coverage inclusion for that data produces a false periodicity.**

This is what makes the deleted `covers` field a soundness matter rather than a
presentational one: with the coverage inclusion available, §5's
`claim43_periodOn_of_sweep` — itself `sorry`-free — concludes that `rowConfig` is
`(0,1)`-periodic on all of `ℤ²`, contradicting `rowConfig (0,1) = 0 ≠ 1 = rowConfig (0,0)`. -/
theorem sweep_covers_failure_gives_False
    (hcov : refK ⊆ halfStripFrom refB (0, 1) 1 ∪ (⋃ i, Set.range (refEnum i))) : False := by
  have hper : PeriodOn rowConfig refK (((1 * 1 : ℕ) : ℤ) • ((0, 1) : ℤ × ℤ)) :=
    claim43_periodOn_of_sweep (self_mem_orbitClosure rowConfig) rowConfig_generatesAt
      (((1 * 1 : ℕ) : ℤ) • ((0, 1) : ℤ × ℤ))
      (agree_T_on_halfStripFrom refHqper 1) refEnum refWindow hcov
  have h0 := hper (0, 0) (Set.mem_univ _) (Set.mem_univ _)
  have e : ((0, 0) : ℤ × ℤ) + ((1 * 1 : ℕ) : ℤ) • ((0, 1) : ℤ × ℤ) = (0, 1) := by
    apply Prod.ext <;> simp
  rw [e] at h0
  simp only [rowConfig] at h0
  rw [if_neg (by decide), if_pos (by decide)] at h0
  exact absurd h0 (by decide)

/-! ### §10.2 A `SweepData` satisfying every field, `covers` included -/

/-- The quadrant `{(n,m) : n ≥ 0, m ≥ 1}`. -/
def upperQuad : Set (ℤ × ℤ) := {z | 0 ≤ z.1 ∧ 1 ≤ z.2}

theorem isLatticeConvexRegion_upperQuad : IsLatticeConvexRegion upperQuad := by
  refine ⟨{p : ℝ × ℝ | 0 ≤ p.1 ∧ 1 ≤ p.2}, ?_, ?_, ?_⟩
  · rintro p ⟨hp1, hp2⟩ r ⟨hr1, hr2⟩ α β hα hβ _
    refine ⟨?_, ?_⟩
    · show (0 : ℝ) ≤ α * p.1 + β * r.1
      exact add_nonneg (mul_nonneg hα hp1) (mul_nonneg hβ hr1)
    · show (1 : ℝ) ≤ α * p.2 + β * r.2
      have e1 : α * 1 ≤ α * p.2 := mul_le_mul_of_nonneg_left hp2 hα
      have e2 : β * 1 ≤ β * r.2 := mul_le_mul_of_nonneg_left hr2 hβ
      linarith
  · exact (isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_const continuous_snd)
  · ext z
    simp only [Set.mem_preimage, toReal, upperQuad, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

theorem isRegion_upperQuad : IsRegion upperQuad (1, 0) (0, 1) := by
  refine ⟨isLatticeConvexRegion_upperQuad, ⟨(0, 1), ?_⟩, ⟨(0, 1), ?_⟩⟩
  · intro k
    refine ⟨?_, ?_⟩
    · show (0 : ℤ) ≤ 0 + (k : ℤ) * 1
      omega
    · show (1 : ℤ) ≤ 1 + (k : ℤ) * 0
      omega
  · intro k
    refine ⟨?_, ?_⟩
    · show (0 : ℤ) ≤ 0 + (k : ℤ) * 0
      omega
    · show (1 : ℤ) ≤ 1 + (k : ℤ) * 1
      omega

theorem upperQuad_nonempty : upperQuad.Nonempty := ⟨(0, 1), le_refl 0, le_refl 1⟩

/-- Base of the seed half-strip: the origin, so the seed is the left edge column
`{(0,t) : t ≥ 1}` of `upperQuad`. -/
def goodB : Finset (ℤ × ℤ) := {(0, 0)}

/-- The enumeration: line `i` is the row `m = i + 1`, swept rightwards from `(1, i+1)`. -/
def goodEnum : ℕ → ℕ → ℤ × ℤ := fun i j => ((j : ℤ) + 1, (i : ℤ) + 1)

theorem mem_goodStrip {t : ℤ} (ht : 1 ≤ t) :
    ((0, t) : ℤ × ℤ) ∈ halfStripFrom goodB (0, 1) 1 := by
  refine ⟨(0, 0), by simp [goodB], t, ht, ?_⟩
  simp

/-- The window condition: `(j+1, i+1)` is conquered from `(j, i+1)`, which is the seed
column when `j = 0` and the previously conquered point of the same line when `j ≥ 1`. -/
theorem goodWindow : ∀ i j : ℕ, ∀ z ∈ Swin.erase (0, 0),
    z + (goodEnum i j - (0, 0)) ∈
      halfStripFrom goodB (0, 1) 1 ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (goodEnum i'))
        ∪ (goodEnum i '' {j' | j' < j}) := by
  intro i j z hz
  rw [swin_erase_eq hz]
  have e : ((-1, 0) : ℤ × ℤ) + (goodEnum i j - (0, 0)) = ((j : ℤ), (i : ℤ) + 1) := by
    apply Prod.ext <;> simp [goodEnum]
  rw [e]
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    refine Or.inl (Or.inl ?_)
    have e0 : (((0 : ℕ) : ℤ), (i : ℤ) + 1) = ((0 : ℤ), (i : ℤ) + 1) := by norm_num
    rw [e0]
    exact mem_goodStrip (by omega)
  · refine Or.inr ⟨j - 1, show j - 1 < j by omega, ?_⟩
    apply Prod.ext <;> simp [goodEnum] <;> omega

/-- **Coverage holds**, and genuinely uses both the seed (the column `n = 0`) and the
enumeration (everything with `n ≥ 1`). -/
theorem goodCovers :
    upperQuad ⊆ halfStripFrom goodB (0, 1) 1 ∪ (⋃ i, Set.range (goodEnum i)) := by
  rintro ⟨n, m⟩ ⟨hn, hm⟩
  simp only at hn hm
  rcases eq_or_lt_of_le hn with h0 | h1
  · refine Set.mem_union_left _ ?_
    have e : ((n, m) : ℤ × ℤ) = ((0, m) : ℤ × ℤ) := by
      apply Prod.ext <;> simp <;> omega
    rw [e]
    exact mem_goodStrip hm
  · refine Set.mem_union_right _ ?_
    refine Set.mem_iUnion.mpr ⟨(m - 1).toNat, (n - 1).toNat, ?_⟩
    apply Prod.ext <;> simp [goodEnum] <;> omega

theorem goodHqper : ∀ g ∈ goodB, ∀ t : ℤ, (1 : ℤ) ≤ t →
    rowConfig (g + (t + ((1 : ℕ) : ℤ)) • ((0, 1) : ℤ × ℤ))
      = rowConfig (g + t • ((0, 1) : ℤ × ℤ)) := by
  intro g hg t ht
  have hg' : g = ((0, 0) : ℤ × ℤ) := by simpa [goodB] using hg
  subst hg'
  have h1 : ((0, 0) : ℤ × ℤ) + (t + ((1 : ℕ) : ℤ)) • ((0, 1) : ℤ × ℤ) = (0, t + 1) := by
    simp
  have h2 : ((0, 0) : ℤ × ℤ) + t • ((0, 1) : ℤ × ℤ) = (0, t) := by simp
  rw [h1, h2]
  simp only [rowConfig]
  rw [if_neg (by omega), if_neg (by omega)]

/-- **`SweepData` is satisfiable**, with a non-degenerate window, an infinite region, an
infinite family of lines, and `covers` holding non-trivially. -/
def goodSweepData :
    SweepData rowConfig rowConfig (1, 0) (0, 1) (Set.univ : Set (ℤ × ℤ)) goodB 1 1 where
  K := upperQuad
  subset_R := Set.subset_univ _
  isRegion := isRegion_upperQuad
  nonempty := upperQuad_nonempty
  t₀ := 1
  t₀_pos := Nat.one_pos
  S := Swin
  a := (0, 0)
  generates := rowConfig_generatesAt
  enum := goodEnum
  window := goodWindow
  covers := goodCovers

/-- The engine runs on `goodSweepData` and the periodicity it outputs is true. -/
theorem goodSweepData_periodOn :
    PeriodOn rowConfig upperQuad (((1 * 1 : ℕ) : ℤ) • ((0, 1) : ℤ × ℤ)) :=
  claim43_periodOn_of_sweep (self_mem_orbitClosure rowConfig) rowConfig_generatesAt
    (((1 * 1 : ℕ) : ℤ) • ((0, 1) : ℤ × ℤ))
    (agree_T_on_halfStripFrom goodHqper 1) goodEnum goodWindow goodCovers

/-- `hsweep_of_sweepData` fires end-to-end on `goodSweepData`. -/
theorem goodSweepData_hsweep :
    ∃ K : Set (ℤ × ℤ), K ⊆ (Set.univ : Set (ℤ × ℤ)) ∧ IsRegion K (1, 0) (0, 1) ∧
      K.Nonempty ∧ ∃ t₀ : ℕ, 0 < t₀ ∧
        PeriodOn rowConfig K (((t₀ * 1 : ℕ) : ℤ) • ((0, 1) : ℤ × ℤ)) :=
  hsweep_of_sweepData (self_mem_orbitClosure rowConfig) goodSweepData goodHqper

/-! ## §11. `exists_sweepData` is **false as stated**, not merely unproved

The module docstring above describes `exists_sweepData` as a construction problem with four
missing ingredients, "item 2 (the region construction) being the binding constraint".  That
description is wrong: no region construction, and no amount of work on items 1, 3, 4, can
discharge `exists_sweepData`, because the statement is refutable.  This section is the
kernel-checked refutation.

### The defect

`SweepData` carries the field

    generates : GeneratesAt η S a

but `exists_sweepData` quantifies over **every** `η : Config A` subject only to
`hx : x ∈ orbitClosure η`.  Nothing in its hypotheses says that `η` has a generating window
at all.  In Colle's §4 that is supplied by the ambient standing hypotheses of Lemma 4.1 —
low complexity (`P η S ≤ P η Q + p`) plus Lemma 2.3 — which produce a nonzero annihilator
and hence a generating window.  None of that survived into this signature.

A configuration with **no** generating window is easy to exhibit: `deltaConfig`, the
indicator of the single lattice point `(0,0)`.  Its orbit closure contains both the all-zero
configuration (push any finite window off the origin) and the indicator of `{a}` for every
`a`; those two agree off `a` and differ at `a`, so `GeneratesAt deltaConfig S a` fails for
*every* finite `S` and every `a`.  Hence `SweepData deltaConfig deltaConfig u u' R B t₁ q`
is uninhabited for **all** `u, u', R, B, t₁, q` — including entirely non-degenerate ones
(`R = ℤ²`, `B = {(0,0)}`, `t₁ = q = 1`, with `hqper` genuinely true, not vacuous).

So this is not the empty-`R` degeneracy: the `generates` field alone is unsatisfiable, and
`K`, `isRegion`, `nonempty`, `covers` never come into it.

### Consequence for the file, and for the repository

`exists_sweepData`'s `sorry` is standing in for a falsehood, exactly as the `sorry` that
§10 removed from `sweepData_covers` was.  Therefore `claim43_hsweep`, which is built on it
and which is advertised as ready to be passed to `Nivat.Colle41.lemma41_of_sweep`, is a
false theorem too; `claim43_hsweep_is_false` below refutes it directly (there the empty-`R`
degeneracy suffices, since `claim43_hsweep` does not expose the `generates` field).

Nothing in §1–§9 is affected: the sweep engine (`sweep_induction`, `multi_line_sweep`,
`claim43_periodOn_of_sweep`, `hsweep_of_sweepData`, `ray_closure_of_period`) is `sorry`-free
and takes `SweepData` as a *hypothesis*, so it is vacuously safe.  The damage is confined to
the two statements that claim to *produce* a `SweepData`.

### What the repair has to be

`exists_sweepData` and `claim43_hsweep` must gain the hypotheses Colle actually has, at
minimum an `η`-generating window (`∃ S a, GeneratesAt η S a`, or the low-complexity
hypothesis that yields it via Lemma 2.3) and enough about `R` to make a nonempty region
inside it possible.  That is a signature change, deliberately **not** made here. -/

/-- The indicator of the single lattice point `(0,0)`. -/
def deltaConfig : Config ℤ := fun z => if z = (0, 0) then 1 else 0

/-- The all-zero configuration lies in the orbit closure of `deltaConfig`: every finite
window can be translated clear of the origin. -/
theorem zero_mem_orbitClosure_delta :
    (fun _ => (0 : ℤ)) ∈ orbitClosure deltaConfig := by
  classical
  intro W
  refine ⟨((((W.sup fun w => (w.1).natAbs) + 1 : ℕ) : ℤ), 0), ?_⟩
  intro w hw
  have hle : (w.1).natAbs ≤ W.sup fun w : ℤ × ℤ => (w.1).natAbs :=
    Finset.le_sup (f := fun w : ℤ × ℤ => (w.1).natAbs) hw
  show (0 : ℤ) = deltaConfig _
  simp only [deltaConfig]
  rw [if_neg]
  intro hcon
  have h1 : (((W.sup fun w : ℤ × ℤ => (w.1).natAbs) + 1 : ℕ) : ℤ) + w.1 = 0 :=
    congrArg Prod.fst hcon
  omega

/-- The indicator of `{a}`, written as a translate of `deltaConfig`. -/
theorem delta_translate_apply (a z : ℤ × ℤ) :
    T (-a) deltaConfig z = if z = a then (1 : ℤ) else 0 := by
  have hiff : (z + -a = ((0, 0) : ℤ × ℤ)) ↔ (z = a) := by
    constructor
    · intro h
      have h1 : z.1 + -a.1 = 0 := congrArg Prod.fst h
      have h2 : z.2 + -a.2 = 0 := congrArg Prod.snd h
      exact Prod.ext (by omega) (by omega)
    · rintro rfl
      exact Prod.ext (show z.1 + -z.1 = (0 : ℤ) by omega)
        (show z.2 + -z.2 = (0 : ℤ) by omega)
  show deltaConfig (z + -a) = _
  simp only [deltaConfig]
  exact if_congr hiff rfl rfl

/-- **`deltaConfig` has no generating window.**  For every finite `S` and every `a`, the
all-zero configuration and the indicator of `{a}` both lie in `orbitClosure deltaConfig`,
agree on `S.erase a`, and differ at `a`. -/
theorem no_generatesAt_delta (S : Finset (ℤ × ℤ)) (a : ℤ × ℤ) :
    ¬ GeneratesAt deltaConfig S a := by
  rintro ⟨-, hgen⟩
  have hagree : ∀ z ∈ S.erase a, (fun _ => (0 : ℤ)) z = T (-a) deltaConfig z := by
    intro z hz
    rw [delta_translate_apply, if_neg (Finset.mem_erase.mp hz).1]
  have key := hgen _ zero_mem_orbitClosure_delta _ (T_mem_orbitClosure _ _) hagree
  rw [delta_translate_apply, if_pos rfl] at key
  exact absurd key (by decide)

/-- **`SweepData` for `deltaConfig` is uninhabited, for every choice of the remaining
parameters.**  Only the `generates` field is used; the region data is irrelevant. -/
theorem no_sweepData_delta {u u' : ℤ × ℤ} {R : Set (ℤ × ℤ)} {B : Finset (ℤ × ℤ)}
    {t₁ : ℤ} {q : ℕ} :
    ¬ Nonempty (SweepData deltaConfig deltaConfig u u' R B t₁ q) := by
  rintro ⟨d⟩
  exact no_generatesAt_delta d.S d.a d.generates

/-- The seed hypothesis `hqper` of `exists_sweepData` holds **non-vacuously** for
`deltaConfig` over the base `{(0,0)}`, direction `(0,1)`, `t₁ = 1`, `q = 1`: the column
`{(0,t) : t ≥ 1}` misses the origin, so `deltaConfig` is constantly `0` on it. -/
theorem delta_hqper : ∀ g ∈ ({(0, 0)} : Finset (ℤ × ℤ)), ∀ t : ℤ, (1 : ℤ) ≤ t →
    deltaConfig (g + (t + ((1 : ℕ) : ℤ)) • ((0, 1) : ℤ × ℤ))
      = deltaConfig (g + t • ((0, 1) : ℤ × ℤ)) := by
  intro g hg t ht
  have hg' : g = ((0, 0) : ℤ × ℤ) := by simpa using hg
  subst hg'
  have h1 : ((0, 0) : ℤ × ℤ) + (t + ((1 : ℕ) : ℤ)) • ((0, 1) : ℤ × ℤ) = (0, t + 1) := by
    simp
  have h2 : ((0, 0) : ℤ × ℤ) + t • ((0, 1) : ℤ × ℤ) = (0, t) := by simp
  rw [h1, h2]
  simp only [deltaConfig]
  rw [if_neg (by intro h; have := congrArg Prod.snd h; simp only at this; omega),
    if_neg (by intro h; have := congrArg Prod.snd h; simp only at this; omega)]

/-- **The statement of `exists_sweepData` is false.**

The `∀`-form below is `exists_sweepData` with its implicit binders made explicit and `A`
specialised to `Type`; since `exists_sweepData` asserts the statement for every universe,
refuting the `Type` instance refutes it.  The witness has `R = ℤ²`, `B = {(0,0)}`,
`t₁ = q = 1` and a genuinely true (non-vacuous) `hqper`, so the failure is *not* the
degenerate `R = ∅` one — it is the missing generating-window hypothesis. -/
theorem exists_sweepData_is_false :
    ¬ (∀ (A : Type) (η x : Config A), x ∈ orbitClosure η →
        ∀ (u u' : ℤ × ℤ) (R : Set (ℤ × ℤ)) (B : Finset (ℤ × ℤ)) (t₁ : ℤ) (q : ℕ), 0 < q →
          (∀ g ∈ B, ∀ t : ℤ, t₁ ≤ t → x (g + (t + (q : ℤ)) • u') = x (g + t • u')) →
          Nonempty (SweepData η x u u' R B t₁ q)) := by
  intro h
  exact no_sweepData_delta
    (h ℤ deltaConfig deltaConfig (self_mem_orbitClosure _)
      (1, 0) (0, 1) Set.univ {(0, 0)} 1 1 Nat.one_pos delta_hqper)

/-- **The statement of `claim43_hsweep` is false too.**

`claim43_hsweep` does not expose the `generates` field, so the refutation above does not
apply verbatim; but it also places no constraint on `R`, and asserts a *nonempty* `K ⊆ R`.
Taking `R = ∅` (and `B = ∅`, which makes its `hqper` hypothesis vacuously true) contradicts
it outright.  This is the statement advertised as ready to feed
`Nivat.Colle41.lemma41_of_sweep`. -/
theorem claim43_hsweep_is_false :
    ¬ (∀ (A : Type) (η x : Config A), x ∈ orbitClosure η →
        ∀ (u u' : ℤ × ℤ) (R : Set (ℤ × ℤ)) (B : Finset (ℤ × ℤ)) (τ : ℤ) (p : ℕ)
          (q : ℕ), 0 < q →
          (∀ g ∈ B, ∀ t : ℤ, τ + (p : ℤ) ≤ t →
            x (g + (t + (q : ℤ)) • u') = x (g + t • u')) →
          ∃ K : Set (ℤ × ℤ), K ⊆ R ∧ IsRegion K u u' ∧ K.Nonempty ∧
            ∃ t₀ : ℕ, 0 < t₀ ∧ PeriodOn x K (((t₀ * q : ℕ) : ℤ) • u')) := by
  intro h
  obtain ⟨K, hKR, -, ⟨z, hz⟩, -⟩ :=
    h ℤ deltaConfig deltaConfig (self_mem_orbitClosure _)
      (1, 0) (0, 1) (∅ : Set (ℤ × ℤ)) (∅ : Finset (ℤ × ℤ)) 0 0 1 Nat.one_pos
      (by simp)
  exact hKR hz

end Nivat.Colle43
