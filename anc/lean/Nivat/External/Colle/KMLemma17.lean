/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.KariMoutot
import Nivat.External.Colle.Interfaces
import Nivat.External.Colle.KMLemma16
import Nivat.SubseqLimit

/-!
# Kari–Moutot Lemma 17

Formalization of Lemma 17 from:
> J. Kari, E. Moutot, *Decidability and Periodicity of Low Complexity Tilings*,
> Theory of Computing Systems **67** (2023) 125–148, doi `10.1007/s00224-021-10063-8`
> (p. 137)

**Lemma 17** (verbatim): "Subshift `Y` is deterministic in direction `−u`."

## What is proved here

`lemma17_of_maximal_family` is **complete** (no `sorry`, no `axiom`).  It is the paper's
Lemma 17, with the paper's hypotheses made explicit:

* the annihilator is a product of shift-differences `Δ = ∏ᵢ (T^{vᵢ} − 1)` with the `vᵢ`
  pairwise non-parallel (this is what Proposition 13 consumes), and `φ = T^{v 0} − 1` is its
  first factor;
* `u` is perpendicular to `v 0` — the situation Lemma 14 produces;
* a *maximal* family `c₁, …, c_n` of pairwise distinct configurations in `O(c)‾` with
  `φc₁ = ⋯ = φc_n` (`MaximalPhiFamily`), which is the paper's "with `n` as large as possible";
* a *joint* subsequential limit `d₁, …, d_n` of that family along `u` (`JointSubseqLimit`);
* the Lemma 14 half-plane conclusion, taken as the hypothesis `Lemma14HalfPlane`.

Proof structure, following p. 137 lines 77–118:
1. Assume `p ∈ ONED (d i₀)`, i.e. `x ≠ y` in `O(d i₀)‾` agreeing on the closed half-plane.
2. Step (i) — `φx = φy`, via `Nivat.KM.prop13` applied to `c′ = φx − φy`
   (`act_eq_of_agree_halfPlane`).  The paper's translation `τ^t` is not needed: `u ⟂ v 0`
   means `z + v 0` stays in the half-plane.
3. Take a *joint* limit `e₁, …, e_n` of `d₁, …, d_n` along translations realising `x`
   (`exists_joint_orbitClosure_limit`), so `e i₀ = x`.
4. `φe₁ = ⋯ = φe_n` by continuity (`act_eq_of_joint_limit` on `KM16.act_eq_of_jointSubseqLimit`).
5. The `e i` are pairwise distinct, by Lemma 16(b) on every translate of the box `B`
   (`differ_of_joint_limit` on `KM16.distinct_configs_differ_on_translates`).
6. `y` differs from every `e i`: translate `B` inside the *open* half-plane
   (`exists_translate_subset_halfPlane`), where `x` and `y` agree.
7. So `e₁, …, e_n, y` are `n + 1` pairwise distinct configurations in `O(c)‾` with equal
   `φ`-products, contradicting maximality.

Note that Lemma 17's own argument never invokes Lemma 14 *directly* — it only needs that `B`
is finite and can be translated into the half-plane.  The `B_u^k` rectangle-shape issue lives
one level down, inside `Lemma14HalfPlane` / Lemma 16(b).

## What is NOT proved here

* `exists_maximalPhiFamily` (Corollary 15: a maximal family exists) is **proved**, from
  `corollary15` (the `n ≤ |A|^{|B|}` bound) plus `Nat.sSup_mem`.  Its hypotheses had to be
  corrected: the previous signature — finite range, `φ ≠ 0`, `act φ c = 0` — is **false**, and
  is refuted by `not_exists_maximalPhiFamily_of_annihilator`.  See the docstring of
  `exists_maximalPhiFamily` for the loud report.
* `lemma17` — the pre-existing, *weaker* statement formerly consumed by `KMProp18Assembly.lean`
  — is still `sorry`, and is now **unused**.  Part 6 below records the two defects in its
  *signature* (reversed translation direction; arbitrary `d` in place of the `i₀`-th component
  of a joint limit of a maximal family) that make it unreachable from
  `lemma17_of_maximal_family`.

## What Part 6 adds (2026-09-14)

`kmProp18` proves `Nivat.KM.KMProp18` outright — no `sorry`, no new axiom — by running the
paper's §4 route in the paper's translation direction: Kari–Szabados for the product
annihilator, Proposition 13 for a factor `v i₀ ⟂ u`, Lemma 14 for the box, Corollary 15 for the
maximal family, Lemma 16 for the joint limit along `-u`, and `lemma17_of_maximal_family` for the
conclusion.  `Nivat.KM18A.kmProp18` now delegates to it, which closes
`Nivat.Colle.exists_doublyPeriodic_in_orbitClosure` (step 2 of Collé Theorem 1.14).

## Signature change (reported loudly)

`lemma17_of_maximal_family` previously read

```
theorem lemma17_of_maximal_family
    {c : Config ℤ} {φ : LaurentTwo ℤ} {u : ℤ × ℤ} {B : Finset (ℤ × ℤ)}
    (hfin : (Set.range c).Finite) (hφ : φ ≠ 0) (hu : u ≠ 0)
    (hann : act φ c = 0) (hnotu : toReal u ∉ ONED c)
    (h14 : Lemma14HalfPlane c φ B u)
    (fam : MaximalPhiFamily c φ) (hfam_pos : fam.n ≥ 1) :
    ∀ d_seq : Fin fam.n → Config ℤ,
      JointSubseqLimit fam.configs d_seq u → toReal (-u) ∉ ONED (d_seq 0)
```

and did not typecheck (`Fin fam.n` has no `0` when `fam.n` is not literally a successor, and
`KMLemma16` was not imported).  It is **not** provable as stated: for an arbitrary annihilator
`φ` with `act φ c = 0` the paper's step (i) has nothing to feed Proposition 13.  The new
statement replaces `hφ : φ ≠ 0` + `hann : act φ c = 0` by the paper's actual data — `φ` is the
first factor of a product-of-shift-differences annihilator, and `u ⟂ v 0` — replaces the
numeral `0 : Fin fam.n` by an explicit index `i₀`, and drops the unused `hnotu`,
`hfam_pos`.  The `MaximalPhiFamily.maximal` field was also restated (see below).

`MaximalPhiFamily.maximal` previously read

```
  maximal : ∀ e ∈ orbitClosure c, act φ e = act φ (configs 0) → ∃ i, configs i = e
```

which is both ill-typed (`configs 0`) and the wrong statement: the paper's contradiction is
with the *cardinality* `n`, using a family whose common `φ`-value differs from the original
family's.  It now reads

```
  maximal : ∀ (k : ℕ) (f : Fin k → Config ℤ), (∀ i, f i ∈ orbitClosure c) →
    (∀ i j, i ≠ j → f i ≠ f j) → (∀ i j, act φ (f i) = act φ (f j)) → k ≤ n
```

Non-degeneracy of `MaximalPhiFamily` is certified below by `constFamily` (satisfiable),
`constFamily_n_eq_one` (`n` is pinned, not free), `not_maximal_vline` (the `maximal` field is
refutable) and `two_le_n_of_maximalPhiFamily_vline` (so `n` is not a constant of the
structure).
-/

namespace Nivat.KM17

open Nivat KM16

/-! ## Part 1: the joint-limit machinery

Kari–Moutot p. 137: *"Apply the translations `τ₁, τ₂, …` on configurations `d₁, …, d_n` and
take jointly converging subsequences … `e_i = lim_j τ_{k_j}(d_i)` exists for all
`i ∈ {1, …, n}`.  Here, clearly, `e₁ = x`."* -/

/-- **Joint limits along one common translation, for the orbit closure.**

Given `x` in the orbit closure of `g i₀`, the translations that realise the finite windows of
`x` can be applied *simultaneously* to all of `g₁, …, g_n`, and a jointly converging
subsequence extracted; the `i₀`-th limit is `x` itself.

The quantifier order is the point: **one** translation `t` per window `W`, working for **all**
`i` at once.

Proof: the windows form a directed set, so `Filter.atTop` on them is `NeBot`; push an
ultrafilter `𝔲` refining it forward, for each cell `w`, along `V ↦ (i ↦ g i (tr V + w))` valued
in the *finite* type `Fin n → ↥A`.  The pushforward is principal, and its value is the joint
limit at `w`. -/
theorem exists_joint_orbitClosure_limit {n : ℕ} (g : Fin n → Config ℤ)
    (A : Set ℤ) (hA : A.Finite) (hgA : ∀ i z, g i z ∈ A)
    (i₀ : Fin n) (x : Config ℤ) (hx : x ∈ orbitClosure (g i₀)) :
    ∃ e : Fin n → Config ℤ, e i₀ = x ∧
      ∀ W : Finset (ℤ × ℤ), ∃ t : ℤ × ℤ, ∀ i, ∀ w ∈ W, e i w = g i (t + w) := by
  classical
  choose tr htr using hx
  have : Finite ↥A := hA.to_subtype
  set 𝔲 : Ultrafilter (Finset (ℤ × ℤ)) := Ultrafilter.of Filter.atTop with h𝔲
  -- For each cell `w`, the joint value tuple is eventually constant along `𝔲`.
  have key : ∀ w : ℤ × ℤ, ∃ p : Fin n → ↥A,
      {V : Finset (ℤ × ℤ) |
        (fun i => (⟨g i (tr V + w), hgA i (tr V + w)⟩ : ↥A)) = p} ∈ 𝔲 := by
    intro w
    obtain ⟨p, hp⟩ := Ultrafilter.eq_pure_of_finite
      (Ultrafilter.map
        (fun V : Finset (ℤ × ℤ) => (fun i => (⟨g i (tr V + w), hgA i (tr V + w)⟩ : ↥A))) 𝔲)
    refine ⟨p, ?_⟩
    have hmem : ({p} : Set (Fin n → ↥A)) ∈
        Ultrafilter.map
          (fun V : Finset (ℤ × ℤ) =>
            (fun i => (⟨g i (tr V + w), hgA i (tr V + w)⟩ : ↥A))) 𝔲 := by
      rw [hp]; exact Ultrafilter.mem_pure.mpr rfl
    rwa [Ultrafilter.mem_map] at hmem
  choose p hp using key
  refine ⟨fun i w => (p w i).val, ?_, ?_⟩
  · -- `e i₀ = x`
    funext w
    have hw : {V : Finset (ℤ × ℤ) | w ∈ V} ∈ 𝔲 := by
      refine Ultrafilter.of_le Filter.atTop ?_
      filter_upwards [Filter.mem_atTop ({w} : Finset (ℤ × ℤ))] with V hV
      have hsub : ({w} : Finset (ℤ × ℤ)) ⊆ V := hV
      exact Finset.mem_of_subset hsub (Finset.mem_singleton_self w)
    obtain ⟨V, hV1, hV2⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem hw (hp w))
    have hV2' : (fun i => (⟨g i (tr V + w), hgA i (tr V + w)⟩ : ↥A)) = p w := hV2
    show (p w i₀).val = x w
    rw [htr V w hV1]
    exact (congrArg Subtype.val (congrFun hV2' i₀)).symm
  · -- the joint property
    intro W
    have h2 : (⋂ w ∈ W, {V : Finset (ℤ × ℤ) |
        (fun i => (⟨g i (tr V + w), hgA i (tr V + w)⟩ : ↥A)) = p w}) ∈ 𝔲 :=
      (Filter.biInter_finset_mem W).mpr fun w _ => hp w
    obtain ⟨V, hV⟩ := Ultrafilter.nonempty_of_mem h2
    refine ⟨tr V, fun i w hw => ?_⟩
    have hVw : (fun i => (⟨g i (tr V + w), hgA i (tr V + w)⟩ : ↥A)) = p w :=
      Set.mem_iInter₂.mp hV w hw
    show (p w i).val = g i (tr V + w)
    exact (congrArg Subtype.val (congrFun hVw i)).symm

/-- Each component of a joint limit lies in the orbit closure of its source. -/
theorem mem_orbitClosure_of_joint_limit {n : ℕ} {g e : Fin n → Config ℤ}
    (hjoint : ∀ W : Finset (ℤ × ℤ), ∃ t : ℤ × ℤ, ∀ i, ∀ w ∈ W, e i w = g i (t + w))
    (i : Fin n) : e i ∈ orbitClosure (g i) := by
  intro W
  obtain ⟨t, ht⟩ := hjoint W
  exact ⟨t, ht i⟩

/-- **The `act φ` products pass to the joint limit.**

If all the `g i` have the same `φ`-product then so do all the `e i`.  Evaluate at `z`, take the
window `{z + q | q ∈ supp φ}`, and read off `act φ (e k) z = act φ (g k) (t + z)` for every `k`
from the *one* translation `t` the joint property supplies. -/
theorem act_eq_of_joint_limit {φ : LaurentTwo ℤ} {n : ℕ} {g e : Fin n → Config ℤ}
    (hjoint : ∀ W : Finset (ℤ × ℤ), ∃ t : ℤ × ℤ, ∀ i, ∀ w ∈ W, e i w = g i (t + w))
    (heq : ∀ i j, act φ (g i) = act φ (g j)) (i j : Fin n) :
    act φ (e i) = act φ (e j) := by
  classical
  funext z
  obtain ⟨t, ht⟩ := hjoint (φ.coeff.support.image fun q => z + q)
  have key : ∀ k : Fin n, act φ (e k) z = act φ (g k) (t + z) := by
    intro k
    simp only [act_apply]
    refine Finsupp.sum_congr fun q hq => ?_
    have hmem : z + q ∈ φ.coeff.support.image fun q => z + q :=
      Finset.mem_image.mpr ⟨q, hq, rfl⟩
    rw [ht k (z + q) hmem, show t + (z + q) = t + z + q from by abel]
  show act φ (e i) z = act φ (e j) z
  rw [key i, key j, heq i j]

/-- **Disagreement on every translate of a finite box passes to the joint limit.**

Kari–Moutot p. 137: *"By Lemma 16(b) we have `τ_{k_j}(d_{i₁})|_{B′} ≠ τ_{k_j}(d_{i₂})|_{B′}`
for all `j`, so taking the limit as `j → ∞` gives `e_{i₁}|_{B′} ≠ e_{i₂}|_{B′}`."* -/
theorem differ_of_joint_limit {n : ℕ} {g e : Fin n → Config ℤ} {B : Finset (ℤ × ℤ)}
    (hjoint : ∀ W : Finset (ℤ × ℤ), ∃ t : ℤ × ℤ, ∀ i, ∀ w ∈ W, e i w = g i (t + w))
    (hgB : ∀ i j, i ≠ j → ∀ s : ℤ × ℤ, ∃ z ∈ B.image (· + s), g i z ≠ g j z)
    {i j : Fin n} (hij : i ≠ j) (s : ℤ × ℤ) :
    ∃ z ∈ B.image (· + s), e i z ≠ e j z := by
  classical
  obtain ⟨t, ht⟩ := hjoint (B.image (· + s))
  obtain ⟨z₀, hz₀, hne⟩ := hgB i j hij (s + t)
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz₀
  have hbs : b + s ∈ B.image (· + s) := Finset.mem_image.mpr ⟨b, hb, rfl⟩
  refine ⟨b + s, hbs, ?_⟩
  rw [ht i (b + s) hbs, ht j (b + s) hbs, show t + (b + s) = b + (s + t) from by abel]
  exact hne

/-! ## Part 2: step (i) of the paper's proof

Kari–Moutot p. 138, proof of Lemma 17, step (i), verbatim:

> "(i) First, φx = φy: Because x|_H = y|_H we have φx|_{H−t} = φy|_{H−t} for some t ∈ ℤ².
> Consider c′ = τ^t(φx − φy), so that c′|_H = 0.  As φ₂⋯φ_m annihilates φx and φy, it also
> annihilates c′.  An application of Proposition 13 on configuration c′ in place of c shows
> that O(c′)‾ is deterministic in direction −u.  (Note that −u is not perpendicular to v_j for
> any j ≠ 1, because v₁ and v_j are not parallel and −u is perpendicular to v₁.)  Due to the
> determinism, c′|_H = 0 implies that c′ = 0, that is, φx = φy."

The translation `τ^t` turns out to be unnecessary: because `u ⟂ v 0`, the point `z + v 0` lies
in `H` whenever `z` does, so `φx − φy` already vanishes on all of `H` with `t = 0`.  This is a
simplification of the bookkeeping, not a weakening. -/

/-- `⟨u, u⟩ > 0` for a non-zero lattice vector `u`. -/
private theorem normSq_pos {u : ℤ × ℤ} (hu : u ≠ 0) : 0 < u.1 * u.1 + u.2 * u.2 := by
  have hor : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
    by_cases h1 : u.1 = 0
    · exact Or.inr fun h2 => hu (Prod.ext h1 h2)
    · exact Or.inl h1
  rcases hor with h | h
  · have h1 : 0 < u.1 * u.1 := mul_self_pos.mpr h
    have h2 : 0 ≤ u.2 * u.2 := mul_self_nonneg _
    linarith
  · have h1 : 0 ≤ u.1 * u.1 := mul_self_nonneg _
    have h2 : 0 < u.2 * u.2 := mul_self_pos.mpr h
    linarith

/-- Two lattice vectors perpendicular to the same non-zero `u` are parallel. -/
private theorem det_eq_zero_of_perp {u a b : ℤ × ℤ} (hu : u ≠ 0)
    (ha : a.1 * u.1 + a.2 * u.2 = 0) (hb : b.1 * u.1 + b.2 * u.2 = 0) : det a b = 0 := by
  have h1 : u.1 * det a b = 0 := by
    simp only [det]
    linear_combination b.2 * ha - a.2 * hb
  have h2 : u.2 * det a b = 0 := by
    simp only [det]
    linear_combination (-b.1) * ha + a.1 * hb
  by_cases hc : u.1 = 0
  · have hu2 : u.2 ≠ 0 := fun hd => hu (Prod.ext hc hd)
    exact (mul_eq_zero.mp h2).resolve_left hu2
  · exact (mul_eq_zero.mp h1).resolve_left hc

/-- `inner2` against a lattice normal is the integral pairing, cast to `ℝ`. -/
private theorem inner2_toReal_eq (u a : ℤ × ℤ) :
    inner2 (toReal u) a = ((a.1 * u.1 + a.2 * u.2 : ℤ) : ℝ) := by
  show (a.1 : ℝ) * (u.1 : ℝ) + (a.2 : ℝ) * (u.2 : ℝ) = ((a.1 * u.1 + a.2 * u.2 : ℤ) : ℝ)
  push_cast
  ring

/-- Pointwise formula for the elementary factor `T^q − 1`. -/
private theorem act_mono_sub_one_apply (q : ℤ × ℤ) (w : Config ℤ) (z : ℤ × ℤ) :
    act (mono q - 1) w z = w (z + q) - w z := by
  rw [act_sub_left, act_mono, act_one]
  rfl

/-- Peeling the first factor off `Δ = ∏ᵢ (T^{vᵢ} − 1)`. -/
private theorem prodShift_succ {m : ℕ} (v : Fin (m + 1) → ℤ × ℤ) :
    (prodShift v : LaurentTwo ℤ) = (mono (v 0) - 1) * prodShift (Fin.tail v) := by
  simp only [prodShift, Fin.prod_univ_succ]
  rfl

/-- If `g` vanishes on the open half-plane `{z | ⟨z, u⟩ < 0}`, then `0` lies in the orbit
closure of `g`: translating far in the direction `−u` pushes any finite window into the
half-plane.  (This is the "`c′|_H = 0`" half of step (i), packaged for `prop13`.) -/
private theorem zero_mem_orbitClosure_of_vanishing {u : ℤ × ℤ} (hu : u ≠ 0) {g : Config ℤ}
    (hg : ∀ z : ℤ × ℤ, z.1 * u.1 + z.2 * u.2 < 0 → g z = 0) :
    (0 : Config ℤ) ∈ orbitClosure g := by
  classical
  intro W
  set M : ℕ := W.sup fun w => (w.1 * u.1 + w.2 * u.2).natAbs with hM
  refine ⟨(-((M : ℤ) + 1) * u.1, -((M : ℤ) + 1) * u.2), fun w hw => ?_⟩
  have hS : 0 < u.1 * u.1 + u.2 * u.2 := normSq_pos hu
  have hP : w.1 * u.1 + w.2 * u.2 ≤ (M : ℤ) := by
    refine le_trans Int.le_natAbs ?_
    have : (w.1 * u.1 + w.2 * u.2).natAbs ≤ M := by
      rw [hM]
      exact Finset.le_sup (f := fun w : ℤ × ℤ => (w.1 * u.1 + w.2 * u.2).natAbs) hw
    exact_mod_cast this
  have hKS : ((M : ℤ) + 1) * 1 ≤ ((M : ℤ) + 1) * (u.1 * u.1 + u.2 * u.2) := by
    refine mul_le_mul_of_nonneg_left hS ?_
    positivity
  have hlt : (((-((M : ℤ) + 1) * u.1, -((M : ℤ) + 1) * u.2) + w : ℤ × ℤ)).1 * u.1
      + (((-((M : ℤ) + 1) * u.1, -((M : ℤ) + 1) * u.2) + w : ℤ × ℤ)).2 * u.2 < 0 := by
    simp only [Prod.fst_add, Prod.snd_add]
    nlinarith [hP, hKS]
  show (0 : ℤ) = g _
  exact (hg _ hlt).symm

/-- **Kari–Moutot Lemma 17, step (i).**  Let `c` be annihilated by `Δ = ∏ᵢ (T^{vᵢ} − 1)` with
the `vᵢ` pairwise non-parallel, and let `u ≠ 0` be perpendicular to `v 0`.  If `x, y ∈ O(c)‾`
agree on the open half-plane `H = {z | ⟨z, u⟩ < 0}`, then `φ₁ x = φ₁ y` where
`φ₁ = T^{v 0} − 1`. -/
theorem act_eq_of_agree_halfPlane
    {c : Config ℤ} {u : ℤ × ℤ} {m : ℕ} {v : Fin (m + 1) → ℤ × ℤ}
    (hu : u ≠ 0)
    (hnp : Pairwise fun i j => det (v i) (v j) ≠ 0)
    (hann : act (prodShift v) c = 0)
    (hperp : (v 0).1 * u.1 + (v 0).2 * u.2 = 0)
    {x y : Config ℤ} (hx : x ∈ orbitClosure c) (hy : y ∈ orbitClosure c)
    (hagree : ∀ z : ℤ × ℤ, z.1 * u.1 + z.2 * u.2 < 0 → x z = y z) :
    act (mono (v 0) - 1) x = act (mono (v 0) - 1) y := by
  classical
  -- The factorisation `Δ = φ₁ · (φ₂⋯φ_m)`.
  have hfac : (prodShift v : LaurentTwo ℤ)
      = (mono (v 0) - 1) * prodShift (Fin.tail v) := prodShift_succ v
  -- `φ₂⋯φ_m` annihilates `φ₁ x`, `φ₁ y`, hence their difference.
  have hax : act (prodShift v) x = 0 := act_eq_zero_of_mem_orbitClosure hann hx
  have hay : act (prodShift v) y = 0 := act_eq_zero_of_mem_orbitClosure hann hy
  have hψx : act (prodShift (Fin.tail v)) (act (mono (v 0) - 1) x) = 0 := by
    rw [← act_mul, mul_comm (prodShift (Fin.tail v)) (mono (v 0) - 1), ← hfac]
    exact hax
  have hψy : act (prodShift (Fin.tail v)) (act (mono (v 0) - 1) y) = 0 := by
    rw [← act_mul, mul_comm (prodShift (Fin.tail v)) (mono (v 0) - 1), ← hfac]
    exact hay
  have hψg : act (prodShift (Fin.tail v))
      (act (mono (v 0) - 1) x - act (mono (v 0) - 1) y) = 0 := by
    rw [act_sub_right, hψx, hψy, sub_zero]
  -- The difference vanishes on the whole open half-plane, with no translation needed:
  -- `u ⟂ v 0` means `z + v 0` lies in `H` whenever `z` does.
  have hgzero : ∀ z : ℤ × ℤ, z.1 * u.1 + z.2 * u.2 < 0 →
      (act (mono (v 0) - 1) x - act (mono (v 0) - 1) y) z = 0 := by
    intro z hz
    have hz2 : (z + v 0).1 * u.1 + (z + v 0).2 * u.2 < 0 := by
      simp only [Prod.fst_add, Prod.snd_add]
      linarith [hperp, hz]
    show act (mono (v 0) - 1) x z - act (mono (v 0) - 1) y z = 0
    rw [act_mono_sub_one_apply, act_mono_sub_one_apply, hagree _ hz, hagree _ hz2]
    ring
  -- Hence `0` lies in the orbit closure of the difference.
  have hzero : (0 : Config ℤ)
      ∈ orbitClosure (act (mono (v 0) - 1) x - act (mono (v 0) - 1) y) :=
    zero_mem_orbitClosure_of_vanishing hu hgzero
  -- `u` is not perpendicular to any `v j`, `j ≠ 0`.
  have hnp' : Pairwise fun i j => det (Fin.tail v i) (Fin.tail v j) ≠ 0 := by
    intro i j hij
    exact hnp fun hc => hij (Fin.succ_injective _ hc)
  have hperp' : ∀ i : Fin m, inner2 (toReal u) (Fin.tail v i) ≠ 0 := by
    intro i hc
    have hz : (Fin.tail v i).1 * u.1 + (Fin.tail v i).2 * u.2 = 0 := by
      have h := (inner2_toReal_eq u (Fin.tail v i)).symm.trans hc
      exact_mod_cast h
    have hd : det (v 0) (v i.succ) = 0 := det_eq_zero_of_perp hu hperp hz
    exact hnp (Ne.symm (Fin.succ_ne_zero i)) hd
  -- Proposition 13: determinism in direction `u` forces the difference to be `0`.
  have hgg : act (mono (v 0) - 1) x - act (mono (v 0) - 1) y = 0 := by
    refine Nivat.KM.prop13 hnp' hψg (Nivat.KM.toReal_ne_zero hu) hperp' _
      (self_mem_orbitClosure _) 0 hzero ?_
    intro z hz
    have hz' : z.1 * u.1 + z.2 * u.2 < 0 := by
      rw [inner2_toReal_eq] at hz
      exact_mod_cast hz
    exact hgzero z hz'
  exact sub_eq_zero.mp hgg

/-! ## Part 3: the maximal family -/

/-- **Maximal φ-multiplicity family**.  Kari–Moutot p. 137: "Let `c₁, …, c_n ∈ X` be pairwise
distinct such that `φc₁ = ⋯ = φc_n`, with `n` as large as possible.  By Corollary 15 such a
maximal `n` exists."

The `maximal` field is the *cardinality* form: no family of pairwise distinct configurations
in `O(c)‾` with a common `φ`-product is longer than `n`.  It deliberately does **not** require
that common value to be `act φ (configs i)` — the paper's contradiction produces a family with
a different common value. -/
structure MaximalPhiFamily (c : Config ℤ) (φ : LaurentTwo ℤ) where
  n : ℕ
  configs : Fin n → Config ℤ
  in_orbit : ∀ i, configs i ∈ orbitClosure c
  distinct : ∀ i j, i ≠ j → configs i ≠ configs j
  equal_phi : ∀ i j, act φ (configs i) = act φ (configs j)
  maximal : ∀ (k : ℕ) (f : Fin k → Config ℤ), (∀ i, f i ∈ orbitClosure c) →
    (∀ i j, i ≠ j → f i ≠ f j) → (∀ i j, act φ (f i) = act φ (f j)) → k ≤ n

/-! ### Non-degeneracy of `MaximalPhiFamily`

A structure nobody satisfies makes the lemma worthless; a `maximal` field everything satisfies
makes it hollow.  The four results below rule out both. -/

/-- Two distinct indices in `Fin k` whenever `1 < k`. -/
private theorem zero_ne_one_fin {k : ℕ} (h0 : 0 < k) (h1 : 1 < k) :
    (⟨0, h0⟩ : Fin k) ≠ ⟨1, h1⟩ := fun h => by
  have := congrArg Fin.val h
  simp at this

/-- A family of pairwise distinct configurations inside `orbitClosure BL.const0` has at most
one member. -/
theorem le_one_of_mem_orbitClosure_const0 {k : ℕ} (f : Fin k → Config ℤ)
    (hmem : ∀ i, f i ∈ orbitClosure BL.const0) (hdist : ∀ i j, i ≠ j → f i ≠ f j) : k ≤ 1 := by
  by_contra hk
  have h0 : 0 < k := by omega
  have h1 : 1 < k := by omega
  exact hdist ⟨0, h0⟩ ⟨1, h1⟩ (zero_ne_one_fin h0 h1)
    ((BL.const0_orbitClosure_eq (hmem ⟨0, h0⟩)).trans
      (BL.const0_orbitClosure_eq (hmem ⟨1, h1⟩)).symm)

/-- **(W1) Satisfiability.**  The one-element family `(BL.const0)` is a `MaximalPhiFamily` for
`BL.const0` and *any* `φ`. -/
def constFamily (φ : LaurentTwo ℤ) : MaximalPhiFamily BL.const0 φ where
  n := 1
  configs := fun _ => BL.const0
  in_orbit := fun _ => self_mem_orbitClosure _
  distinct := fun i j hij => absurd (Subsingleton.elim i j) hij
  equal_phi := fun _ _ => rfl
  maximal := fun _ f hmem hdist _ => le_one_of_mem_orbitClosure_const0 f hmem hdist

/-- **(W2) `n` is pinned, not free.**  Over `BL.const0` the maximality field forces
`n = 1`. -/
theorem constFamily_n_eq_one (φ : LaurentTwo ℤ) (fam : MaximalPhiFamily BL.const0 φ) :
    fam.n = 1 := by
  have hge : 1 ≤ fam.n :=
    fam.maximal 1 (fun _ => BL.const0) (fun _ => self_mem_orbitClosure _)
      (fun i j hij => absurd (Subsingleton.elim i j) hij) (fun _ _ => rfl)
  have hle : fam.n ≤ 1 :=
    le_one_of_mem_orbitClosure_const0 fam.configs fam.in_orbit fam.distinct
  omega

/-- `KM.vline` and `BL.const0` differ at the origin. -/
theorem vline_ne_const0 : (KM.vline : Config ℤ) ≠ BL.const0 := by
  intro h
  have := congrFun h ((0 : ℤ), (0 : ℤ))
  simp [KM.vline, BL.const0] at this

/-- The two-element family `![KM.vline, BL.const0]` lies in `orbitClosure KM.vline`. -/
theorem pair_mem_orbitClosure_vline :
    ∀ i, (![KM.vline, BL.const0] : Fin 2 → Config ℤ) i ∈ orbitClosure KM.vline := by
  intro i
  fin_cases i
  · simpa using self_mem_orbitClosure KM.vline
  · simpa using KM.const0_mem_orbitClosure_vline

/-- The two-element family `![KM.vline, BL.const0]` is pairwise distinct. -/
theorem pair_distinct :
    ∀ i j, i ≠ j → (![KM.vline, BL.const0] : Fin 2 → Config ℤ) i ≠ ![KM.vline, BL.const0] j := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · simpa using vline_ne_const0
  · simpa using vline_ne_const0.symm
  · exact absurd rfl hij

/-- `φ = 0` kills every configuration, so the `φ`-values of the pair agree. -/
theorem pair_equal_phi :
    ∀ i j, act (0 : LaurentTwo ℤ) ((![KM.vline, BL.const0] : Fin 2 → Config ℤ) i)
      = act 0 (![KM.vline, BL.const0] j) := by
  intro i j
  rw [act_zero_left, act_zero_left]

/-- **(W3) Refutation.**  The `maximal` field is a real constraint: with `c = KM.vline` and
`φ = 0` the value `n = 1` violates it, witnessed by `![KM.vline, BL.const0]`. -/
theorem not_maximal_vline :
    ¬ (∀ (k : ℕ) (f : Fin k → Config ℤ), (∀ i, f i ∈ orbitClosure KM.vline) →
        (∀ i j, i ≠ j → f i ≠ f j) →
        (∀ i j, act (0 : LaurentTwo ℤ) (f i) = act 0 (f j)) → k ≤ 1) := by
  intro h
  have h2 : (2 : ℕ) ≤ 1 :=
    h 2 ![KM.vline, BL.const0] pair_mem_orbitClosure_vline pair_distinct pair_equal_phi
  omega

/-- **(W4)** Any `MaximalPhiFamily` over `KM.vline` with `φ = 0` has `n ≥ 2`.  Together with
`constFamily_n_eq_one` this shows `n` is not a constant of the structure. -/
theorem two_le_n_of_maximalPhiFamily_vline (fam : MaximalPhiFamily KM.vline 0) : 2 ≤ fam.n :=
  fam.maximal 2 ![KM.vline, BL.const0] pair_mem_orbitClosure_vline pair_distinct pair_equal_phi

/-! ### Kari–Moutot Corollary 15

Kari–Moutot p. 136, verbatim: *"A reason to prove the lemma above is the following corollary,
stating that `X` can only contain a bounded number of configurations that have the same product
with `Δ`:"*

> **Corollary 15**  Let `c₁, …, c_n ∈ X` be pairwise distinct.  If `Δc₁ = ⋯ = Δc_n` then
> `n ≤ |A|^{|B|}`.
>
> *Proof*  Let `H′ = H − t`, for `t ∈ ℤ²`, be a translate of the half plane `H = H_{−u}` such
> that `c₁, …, c_n` are pairwise different on `H′`.  Consider the translated configurations
> `d_i = τ^t(c_i)`.  We have that `d_i ∈ X` are pairwise different on `H` and
> `Δd₁ = ⋯ = Δd_n`.  By Lemma 14, configurations `d_i` must be pairwise different on domain
> `B`.  There are only `|A|^{|B|}` different patterns in domain `B`.

So the bound comes from **Lemma 14** — here the hypothesis `Lemma14HalfPlane`, discharged by
`Nivat.KM16.exists_lemma14HalfPlane_of_det` — and from nothing else.  In particular it is *not*
a consequence of `act φ c = 0` alone; see `not_exists_maximalPhiFamily_of_annihilator`. -/

/-- **Kari–Moutot Corollary 15** (p. 136).  Any family of pairwise distinct configurations in
`O(c)‾` with a common `φ`-product has at most `|A|^{|B|}` members, where `A = range c` is the
alphabet and `B` is the Lemma 14 box.

The translate `t` of the paper's proof is `M • w` for `M` larger than every `⟨p_ij, w⟩`, where
`p_ij` is a cell separating `c_i` from `c_j`: that is exactly *"a translate of the half plane
`H` such that `c₁, …, c_n` are pairwise different on `H′`"*.  Lemma 14 is then used in
contrapositive form — agreeing on `B` would force agreeing on the whole half plane, where the
witnesses `p_ij` now live. -/
theorem corollary15 {c : Config ℤ} {φ : LaurentTwo ℤ} {w : ℤ × ℤ} {B : Finset (ℤ × ℤ)}
    (hw : w ≠ 0) (hfin : (Set.range c).Finite) (h14 : Lemma14HalfPlane c φ B w)
    {k : ℕ} (f : Fin k → Config ℤ) (hmem : ∀ i, f i ∈ orbitClosure c)
    (hdist : ∀ i j, i ≠ j → f i ≠ f j) (heq : ∀ i j, act φ (f i) = act φ (f j)) :
    k ≤ hfin.toFinset.card ^ B.card := by
  classical
  -- A witness cell for every ordered pair of distinct indices.
  have hPex : ∀ q : Fin k × Fin k, ∃ p : ℤ × ℤ, q.1 ≠ q.2 → f q.1 p ≠ f q.2 p := by
    intro q
    by_cases h : q.1 = q.2
    · exact ⟨0, fun hne => absurd h hne⟩
    · obtain ⟨p, hp⟩ := Function.ne_iff.mp (hdist q.1 q.2 h)
      exact ⟨p, fun _ => hp⟩
  choose P hPspec using hPex
  -- The translation `t` that puts every witness cell into `halfPlane w`.
  set M : ℕ := (Finset.univ.sup fun q : Fin k × Fin k => (innerZ (P q) w).toNat) + 1 with hM
  set t : ℤ × ℤ := (M : ℤ) • w with ht
  have hww : 0 < innerZ w w := inner_self_pos hw
  have hkey : ∀ q : Fin k × Fin k, P q - t ∈ KM16.halfPlane w := by
    intro q
    rw [mem_halfPlane_iff_innerZ, innerZ_sub, ht, innerZ_zsmul]
    have h1 : innerZ (P q) w ≤ ((innerZ (P q) w).toNat : ℤ) := Int.self_le_toNat _
    have h2 : (innerZ (P q) w).toNat
        ≤ Finset.univ.sup fun q : Fin k × Fin k => (innerZ (P q) w).toNat :=
      Finset.le_sup (f := fun q : Fin k × Fin k => (innerZ (P q) w).toNat) (Finset.mem_univ q)
    have h2' : ((innerZ (P q) w).toNat : ℤ)
        ≤ ((Finset.univ.sup fun q : Fin k × Fin k => (innerZ (P q) w).toNat : ℕ) : ℤ) := by
      exact_mod_cast h2
    have h3 : (M : ℤ) ≤ (M : ℤ) * innerZ w w :=
      le_mul_of_one_le_right (by positivity) hww
    have h4 : (M : ℤ)
        = ((Finset.univ.sup fun q : Fin k × Fin k => (innerZ (P q) w).toNat : ℕ) : ℤ) + 1 := by
      rw [hM]; push_cast; ring
    linarith
  -- The restriction-to-`B` map into patterns over the alphabet.
  have hval : ∀ (i : Fin k) (z : ℤ × ℤ), T t (f i) z ∈ hfin.toFinset := by
    intro i z
    rw [Set.Finite.mem_toFinset]
    exact mem_range_of_mem_orbitClosure (T_mem_of_mem_orbitClosure (hmem i) t) z
  set g : Fin k → ({x // x ∈ B} → {x // x ∈ hfin.toFinset}) :=
    fun i b => ⟨T t (f i) b.1, hval i b.1⟩ with hg
  have hginj : Function.Injective g := by
    intro i j hij
    by_contra hne
    have hagree : ∀ z ∈ B, T t (f i) z = T t (f j) z := by
      intro z hz
      have := congrFun hij ⟨z, hz⟩
      simpa [hg] using congrArg Subtype.val this
    have hd : T t (f i) ∈ orbitClosure c := T_mem_of_mem_orbitClosure (hmem i) t
    have he : T t (f j) ∈ orbitClosure c := T_mem_of_mem_orbitClosure (hmem j) t
    have hact : act φ (T t (f i)) = act φ (T t (f j)) := by
      rw [act_T, act_T, heq i j]
    have hhalf := h14 _ hd _ he hact hagree
    have hz := hhalf _ (hkey (i, j))
    have hcancel : P (i, j) - t + t = P (i, j) := by abel
    have : f i (P (i, j)) = f j (P (i, j)) := by
      have e1 : T t (f i) (P (i, j) - t) = f i (P (i, j)) := by
        show f i (P (i, j) - t + t) = _
        rw [hcancel]
      have e2 : T t (f j) (P (i, j) - t) = f j (P (i, j)) := by
        show f j (P (i, j) - t + t) = _
        rw [hcancel]
      rw [← e1, ← e2]; exact hz
    exact hPspec (i, j) hne this
  calc k = Fintype.card (Fin k) := (Fintype.card_fin k).symm
    _ ≤ Fintype.card ({x // x ∈ B} → {x // x ∈ hfin.toFinset}) :=
        Fintype.card_le_of_injective g hginj
    _ = hfin.toFinset.card ^ B.card := by
        simp [Fintype.card_coe]

/-- **Corollary 15, packaged as the existence of a maximal family**, from the Lemma 14 box.

The paper, p. 136: *"Let `c₁, …, c_n ∈ X` be pairwise distinct such that `Δc₁ = ⋯ = Δc_n`, with
`n` as large as possible.  By Corollary 15 such a maximal `n` exists."*

`corollary15` bounds the set of achievable family sizes; that set contains `1` (the singleton
family `(c)`), so its `sSup` is achieved (`Nat.sSup_mem`) and is `≥ 1`. -/
theorem exists_maximalPhiFamily_of_lemma14 {c : Config ℤ} {φ : LaurentTwo ℤ} {w : ℤ × ℤ}
    {B : Finset (ℤ × ℤ)} (hw : w ≠ 0) (hfin : (Set.range c).Finite)
    (h14 : Lemma14HalfPlane c φ B w) :
    ∃ fam : MaximalPhiFamily c φ, fam.n ≥ 1 := by
  classical
  set S : Set ℕ := {k | ∃ f : Fin k → Config ℤ, (∀ i, f i ∈ orbitClosure c) ∧
      (∀ i j, i ≠ j → f i ≠ f j) ∧ (∀ i j, act φ (f i) = act φ (f j))} with hS
  have h1 : 1 ∈ S := ⟨fun _ => c, fun _ => self_mem_orbitClosure c,
      fun i j hij => absurd (Subsingleton.elim i j) hij, fun _ _ => rfl⟩
  have hbdd : BddAbove S := by
    refine ⟨hfin.toFinset.card ^ B.card, ?_⟩
    rintro k ⟨f, hf1, hf2, hf3⟩
    exact corollary15 hw hfin h14 f hf1 hf2 hf3
  have hne : S.Nonempty := ⟨1, h1⟩
  obtain ⟨f, hf1, hf2, hf3⟩ := Nat.sSup_mem hne hbdd
  refine ⟨⟨sSup S, f, hf1, hf2, hf3, ?_⟩, ?_⟩
  · intro k g hg1 hg2 hg3
    exact le_csSup hbdd ⟨g, hg1, hg2, hg3⟩
  · exact le_csSup hbdd h1

/-- **Kari–Moutot Corollary 15** in the form Lemma 17 consumes: every configuration of finite
range that is deterministic in a direction `u` perpendicular to the direction `v` of the factor
`φ = T^v − 1` admits a maximal `φ`-family.

### Signature change (reported loudly)

This declaration previously read

```
theorem exists_maximalPhiFamily {c : Config ℤ} {φ : LaurentTwo ℤ}
    (hfin : (Set.range c).Finite) (hφ : φ ≠ 0) (hann : act φ c = 0) :
    ∃ (fam : MaximalPhiFamily c φ), fam.n ≥ 1
```

and was `sorry`.  **That statement is false**, and is refuted below by
`not_exists_maximalPhiFamily_of_annihilator`: at `c = KM.vline` and `φ = T^{(0,1)} − 1` all the
horizontal translates `T^{(i,0)}(vline)` are pairwise distinct elements of `O(vline)‾` with
`φ`-product `0`, so the achievable family sizes are unbounded and no maximal `n` exists.

The missing hypothesis is exactly the one the paper carries through all of §4 and that
Corollary 15 inherits from Lemma 14: `u` is a **direction of determinism** of `O(c)‾`
(`hdet`), and `v ⟂ u` (`hperp`).  The counterexample is consistent with the paper — for
`v = (0,1)` perpendicularity forces `u` horizontal, and the horizontal directions are precisely
`ONED vline` (`Nivat.KM.vline_ONED_horizontal_pos`), i.e. precisely the directions in which
`O(vline)‾` is *not* deterministic.

The hypotheses here are those of `Nivat.KM16.exists_lemma14HalfPlane_of_det`, which is what
supplies the box `B`; `hφ : φ ≠ 0` and `hann : act φ c = 0` are not needed and are dropped. -/
theorem exists_maximalPhiFamily {c : Config ℤ} {φ : LaurentTwo ℤ} {u v : ℤ × ℤ}
    (hfin : (Set.range c).Finite) (hu : u ≠ 0) (hv : v ≠ 0)
    (hperp : innerZ v u = 0) (hphi : φ = mono v - 1) (hdet : toReal u ∉ ONED c) :
    ∃ fam : MaximalPhiFamily c φ, fam.n ≥ 1 := by
  obtain ⟨B, -, -, h14⟩ := exists_lemma14HalfPlane_of_det hfin hu hv hperp hphi hdet
  exact exists_maximalPhiFamily_of_lemma14 (neg_ne_zero.mpr hu) hfin h14

/-! ### The previous signature of `exists_maximalPhiFamily` is refuted -/

/-- `T^u − 1` is a nonzero Laurent polynomial for `u ≠ 0`: it fails to annihilate the linear
configuration `z ↦ ⟨z, u⟩`. -/
private theorem mono_sub_one_ne_zero (u : ℤ × ℤ) (hu : u ≠ 0) :
    (mono u - 1 : LaurentTwo ℤ) ≠ 0 := by
  intro h
  have hper : u ∈ Per (fun z : ℤ × ℤ => z.1 * u.1 + z.2 * u.2) := by
    rw [← act_mono_sub_one_eq_zero_iff, h, act_zero_left]
  rw [mem_Per_iff] at hper
  have := congrFun hper 0
  simp [T] at this
  have hpos : 0 < u.1 * u.1 + u.2 * u.2 := KM16.inner_self_pos hu
  omega

/-- **The old signature of `exists_maximalPhiFamily` is false.**  Finiteness of the alphabet,
`φ ≠ 0` and `act φ c = 0` do *not* bound the number of configurations of `O(c)‾` sharing a
`φ`-product.

Witness: `c = KM.vline` (the indicator of the column `x = 0`, of range `{0,1}`), and
`φ = T^{(0,1)} − 1`, which annihilates `vline` because `vline` is invariant under vertical
translation (`Nivat.KM.vline_per`).  For every `m` the `m` horizontal translates
`T^{(i,0)}(vline)`, `i < m`, are pairwise distinct members of `O(vline)‾` and each is annihilated
by `φ`, so they all share the `φ`-product `0`.  Any `MaximalPhiFamily` would therefore satisfy
`m ≤ n` for every `m`.

This is *not* a counterexample to Kari–Moutot Corollary 15: the paper's standing hypothesis is
that `u` is a direction of determinism with `v ⟂ u`, and here `v = (0,1)` forces `u` horizontal,
where `O(vline)‾` is not deterministic (`Nivat.KM.vline_ONED_horizontal_pos`).  It is a
counterexample to the *statement that used to carry this name*. -/
theorem not_exists_maximalPhiFamily_of_annihilator :
    ¬ ∀ (c : Config ℤ) (φ : LaurentTwo ℤ), (Set.range c).Finite → φ ≠ 0 → act φ c = 0 →
      ∃ fam : MaximalPhiFamily c φ, fam.n ≥ 1 := by
  intro h
  have hne : (mono ((0 : ℤ), (1 : ℤ)) - 1 : LaurentTwo ℤ) ≠ 0 :=
    mono_sub_one_ne_zero _ (by intro hc; exact absurd (congrArg Prod.snd hc) (by norm_num))
  have hann : act (mono ((0 : ℤ), (1 : ℤ)) - 1) KM.vline = 0 :=
    (act_mono_sub_one_eq_zero_iff _ _).mpr KM.vline_per
  obtain ⟨fam, -⟩ := h KM.vline _ KM.vline_range_finite hne hann
  have key : ∀ m : ℕ, m ≤ fam.n := by
    intro m
    refine fam.maximal m (fun i => T (((i : ℕ) : ℤ), (0 : ℤ)) KM.vline) ?_ ?_ ?_
    · exact fun i => T_mem_orbitClosure _ _
    · intro i j hij hcon
      have hval := congrFun hcon ((-((i : ℕ) : ℤ)), (0 : ℤ))
      have hij' : ((i : ℕ) : ℤ) ≠ ((j : ℕ) : ℤ) := by
        exact_mod_cast fun hc => hij (Fin.ext hc)
      simp [T, KM.vline] at hval
      omega
    · intro i j
      rw [act_T, act_T, hann]
      funext z
      rfl
  have := key (fam.n + 1)
  omega

/-! ### Non-degeneracy of `exists_maximalPhiFamily`: an instance with `n ≥ 2`

`constFamily` only shows the structure is inhabited, and it is inhabited at `n = 1`.  The
obligation for Corollary 15 is sharper: the theorem must produce, for *some* admissible `c` and
`φ`, a family that is genuinely bigger than a singleton.  The witness below is the horizontal
stripe configuration of period `2`. -/

/-- The `2`-periodic horizontal stripe configuration `(x, y) ↦ y mod 2`. -/
def stripe : Config ℤ := fun z => z.2 % 2

theorem stripe_range_finite : (Set.range stripe).Finite := by
  refine Set.Finite.subset ((Set.finite_singleton (1 : ℤ)).insert 0) ?_
  rintro _ ⟨z, rfl⟩
  have : z.2 % 2 = 0 ∨ z.2 % 2 = 1 := Int.emod_two_eq_zero_or_one z.2
  rcases this with h | h <;> simp [stripe, h]

/-- `stripe` is invariant under horizontal translation, so `T^{(1,0)} − 1` annihilates it. -/
theorem stripe_per : ((1 : ℤ), (0 : ℤ)) ∈ Per stripe := by
  rw [mem_Per_iff]
  funext z
  show stripe (z + ((1 : ℤ), (0 : ℤ))) = stripe z
  simp [stripe]

/-- The orbit closure of `stripe` has exactly two elements: reading the value at the origin
pins which of the two phases a member is. -/
theorem stripe_orbit_two {x : Config ℤ} (hx : x ∈ orbitClosure stripe) :
    x = stripe ∨ x = T ((0 : ℤ), (1 : ℤ)) stripe := by
  by_cases h0 : x ((0 : ℤ), (0 : ℤ)) = 0
  · left
    funext z
    obtain ⟨t, ht⟩ := hx {((0 : ℤ), (0 : ℤ)), z}
    have h1 := ht ((0 : ℤ), (0 : ℤ)) (by simp)
    have h2 := ht z (by simp)
    simp only [stripe, Prod.snd_add] at h1 h2 ⊢
    omega
  · right
    funext z
    obtain ⟨t, ht⟩ := hx {((0 : ℤ), (0 : ℤ)), z}
    have h1 := ht ((0 : ℤ), (0 : ℤ)) (by simp)
    have h2 := ht z (by simp)
    simp only [stripe, T, Prod.snd_add] at h0 h1 h2 ⊢
    omega

theorem stripe_ne_shift : (stripe : Config ℤ) ≠ T ((0 : ℤ), (1 : ℤ)) stripe := by
  intro hc
  have := congrFun hc ((0 : ℤ), (0 : ℤ))
  simp [stripe, T] at this

/-- `O(stripe)‾` is deterministic in **every** direction: its two members differ at every cell,
so no two distinct members can agree on a closed half plane. -/
theorem stripe_not_ONED (u : ℤ × ℤ) : toReal u ∉ ONED stripe := by
  rintro ⟨-, x, hx, y, hy, hxy, hagree⟩
  have h00 : ((0 : ℤ), (0 : ℤ)) ∈ sideOf (toReal u) := by
    simp [sideOf, inner2]
  have hval := hagree _ h00
  rcases stripe_orbit_two hx with rfl | rfl <;> rcases stripe_orbit_two hy with rfl | rfl
  · exact hxy rfl
  · simp [stripe, T] at hval
  · simp [stripe, T] at hval
  · exact hxy rfl

/-- **Non-degeneracy certificate for `exists_maximalPhiFamily`.**  At `c = stripe`,
`u = (0,1)`, `v = (1,0)` and `φ = T^{(1,0)} − 1` — all hypotheses of `exists_maximalPhiFamily`
hold — the maximal family it produces has `n ≥ 2`, witnessed by the two phases `stripe` and
`T^{(0,1)}(stripe)`, which are distinct and both annihilated by `φ`.

So Corollary 15 as proved here is not the trivial statement about singleton orbit closures. -/
theorem two_le_n_of_exists_maximalPhiFamily_stripe :
    ∃ fam : MaximalPhiFamily stripe (mono ((1 : ℤ), (0 : ℤ)) - 1), 2 ≤ fam.n := by
  obtain ⟨fam, -⟩ := exists_maximalPhiFamily (c := stripe)
      (φ := mono ((1 : ℤ), (0 : ℤ)) - 1) (u := ((0 : ℤ), (1 : ℤ))) (v := ((1 : ℤ), (0 : ℤ)))
      stripe_range_finite
      (by intro hc; exact absurd (congrArg Prod.snd hc) (by norm_num))
      (by intro hc; exact absurd (congrArg Prod.fst hc) (by norm_num))
      (by simp [innerZ]) rfl (stripe_not_ONED _)
  refine ⟨fam, fam.maximal 2 ![stripe, T ((0 : ℤ), (1 : ℤ)) stripe] ?_ ?_ ?_⟩
  · intro i
    fin_cases i
    · simpa using self_mem_orbitClosure stripe
    · simpa using T_mem_orbitClosure stripe ((0 : ℤ), (1 : ℤ))
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa using stripe_ne_shift
    · simpa using stripe_ne_shift.symm
    · exact absurd rfl hij
  · have hz : act (mono ((1 : ℤ), (0 : ℤ)) - 1) stripe = 0 :=
      (act_mono_sub_one_eq_zero_iff _ _).mpr stripe_per
    have hz2 : act (mono ((1 : ℤ), (0 : ℤ)) - 1) (T ((0 : ℤ), (1 : ℤ)) stripe) = 0 := by
      rw [act_T, hz]
      funext z
      rfl
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hz, hz2]

/-! ## Part 4: translating a finite box into the open half-plane -/

/-- Every finite box has a translate contained in the open half plane `halfPlane p`.  This is
the paper's *"since `B` is finite, we can choose `B′ = B − t ⊆ H`"*. -/
theorem exists_translate_subset_halfPlane {p : ℤ × ℤ} (hp : p ≠ 0) (B : Finset (ℤ × ℤ)) :
    ∃ s : ℤ × ℤ, ∀ z ∈ B.image (· + s), z ∈ KM16.halfPlane p := by
  classical
  have hS : 0 < p.1 * p.1 + p.2 * p.2 := KM16.inner_self_pos hp
  set K : ℕ := (B.sup fun b => (b.1 * p.1 + b.2 * p.2).natAbs) + 1 with hK
  refine ⟨(-(K : ℤ)) • p, ?_⟩
  intro z hz
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
  rw [KM16.mem_halfPlane_iff]
  have hsmul1 : ((-(K : ℤ)) • p).1 = -(K : ℤ) * p.1 := by
    simp only [Prod.smul_fst, smul_eq_mul]
  have hsmul2 : ((-(K : ℤ)) • p).2 = -(K : ℤ) * p.2 := by
    simp only [Prod.smul_snd, smul_eq_mul]
  have hexp : (b + (-(K : ℤ)) • p).1 * p.1 + (b + (-(K : ℤ)) • p).2 * p.2
      = (b.1 * p.1 + b.2 * p.2) - (K : ℤ) * (p.1 * p.1 + p.2 * p.2) := by
    simp only [Prod.fst_add, Prod.snd_add, hsmul1, hsmul2]
    ring
  rw [hexp]
  have h1 : b.1 * p.1 + b.2 * p.2 ≤ ((b.1 * p.1 + b.2 * p.2).natAbs : ℤ) := Int.le_natAbs
  have h2 : (b.1 * p.1 + b.2 * p.2).natAbs
      ≤ B.sup fun b => (b.1 * p.1 + b.2 * p.2).natAbs :=
    Finset.le_sup (f := fun b : ℤ × ℤ => (b.1 * p.1 + b.2 * p.2).natAbs) hb
  have h2' : ((b.1 * p.1 + b.2 * p.2).natAbs : ℤ)
      ≤ ((B.sup fun b => (b.1 * p.1 + b.2 * p.2).natAbs : ℕ) : ℤ) := by exact_mod_cast h2
  have hKval : (K : ℤ) = ((B.sup fun b => (b.1 * p.1 + b.2 * p.2).natAbs : ℕ) : ℤ) + 1 := by
    rw [hK]; push_cast; ring
  have h3 : b.1 * p.1 + b.2 * p.2 ≤ (K : ℤ) - 1 := by
    rw [hKval]; linarith [h1, h2']
  have h4 : (K : ℤ) ≤ (K : ℤ) * (p.1 * p.1 + p.2 * p.2) :=
    le_mul_of_one_le_right (by positivity) hS
  linarith

/-! ## Part 5. **`lemma17` — deleted 2026-09-16**

A theorem stood here asserting a one-sided determinism conclusion in the `+u` direction
from hypotheses matching KM Lemma 17.  **It was misstated**: the paper defines
`τ^t(c)_n = c_{n−t}` (`scratch/e1_km.txt:118-119`) and takes `d = lim τ^{n_j u}(c₁)`
(`:694-698`), which under this repo's `subseqLimits` (`Nivat/Defs/Orbit.lean:132-133`,
`y w = c(w + n•u)`) lands in `subseqLimits c (-u)`, not `subseqLimits c u`.  It also
omitted the maximal-family premise.

The theorem had **0 code call sites** (all hits in `KMProp18.lean`, `KMProp18Assembly.lean`,
`Theorem114.lean`, `Theorem114Final.lean` were docstrings; grep excluding worktrees/imports/self
confirmed at text level).  It is not in the declaration-level dependency chain of
`nivat_conjecture` or `colle_region` (axiom closure at GATE_LOG.jsonl:37 has no `sorryAx`,
and ColleRegion.lean's import closure — 56 modules — does not contain KMLemma17).

KM Prop 18 is **proved** in this file via `kmProp18` (`:1168`) → `kmProp18_of_perp` (`:1119`)
→ `lemma17_of_lemma14` (`:995`) → `lemma17_of_maximal_family` (`:864`), and the gate is
green modulo sorry count.  See blueprint/NOTE.md for full disposal record.

Given a maximal family `fam` of pairwise distinct configurations in `O(c)‾` with a common
`φ`-product (`φ = T^{v 0} − 1`, the first factor of the annihilator `∏ᵢ (T^{vᵢ} − 1)`), and a
joint subsequential limit `d_seq` of that family along `u`, no direction `p` perpendicular to
`v 0` is a direction of determinism in `O(d_seq i₀)‾`.

Applied with `p = u` and `p = −u` (both perpendicular to `v 0`, since `u` is) this is the
paper's "`Y` is deterministic in direction `−u`" — see `lemma17_twoSided`.

See the module docstring for the loud report of how this signature differs from the (ill-typed
and unprovable) statement that previously carried this name. -/
theorem lemma17_of_maximal_family
    {c : Config ℤ} {u : ℤ × ℤ} {B : Finset (ℤ × ℤ)} {m : ℕ} {v : Fin (m + 1) → ℤ × ℤ}
    {φ : LaurentTwo ℤ} (hφ : φ = mono (v 0) - 1)
    (hfin : (Set.range c).Finite) (hu : u ≠ 0)
    (hnp : Pairwise fun i j => det (v i) (v j) ≠ 0)
    (hann : act (prodShift v) c = 0)
    (h14 : KM16.Lemma14HalfPlane c φ B u)
    (fam : MaximalPhiFamily c φ)
    {d_seq : Fin fam.n → Config ℤ}
    (hjoint : KM16.JointSubseqLimit fam.configs d_seq u)
    (i₀ : Fin fam.n)
    {p : ℤ × ℤ} (hp : p ≠ 0) (hperp : (v 0).1 * p.1 + (v 0).2 * p.2 = 0) :
    toReal p ∉ ONED (d_seq i₀) := by
  classical
  rintro ⟨-, x, hx, y, hy, hne, hagr⟩
  -- the agreement hypothesis, in integer form
  have hagrZ : ∀ z : ℤ × ℤ, z.1 * p.1 + z.2 * p.2 < 0 → x z = y z := by
    intro z hz
    refine hagr z ?_
    show inner2 (toReal p) z ≤ 0
    show (z.1 : ℝ) * ((p.1 : ℤ) : ℝ) + (z.2 : ℝ) * ((p.2 : ℤ) : ℝ) ≤ 0
    have hR : ((z.1 * p.1 + z.2 * p.2 : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hz.le
    push_cast at hR
    linarith
  have hagrHalf : ∀ z ∈ KM16.halfPlane p, x z = y z := fun z hz => hagrZ z hz
  -- everything lives in the orbit closure of `c`
  have hdorb : ∀ i, d_seq i ∈ orbitClosure c := fun i =>
    Nivat.Colle.mem_orbitClosure_trans (fam.in_orbit i) (hjoint.mem_orbitClosure i)
  have hgA : ∀ (i : Fin fam.n) (z : ℤ × ℤ), d_seq i z ∈ Set.range c := by
    intro i z
    obtain ⟨t, ht⟩ := hdorb i {z}
    exact ⟨t + z, (ht z (Finset.mem_singleton_self z)).symm⟩
  -- the joint limit `e₁, …, e_n` of `d₁, …, d_n`, with `e i₀ = x`
  obtain ⟨e, he0, hjl⟩ :=
    exists_joint_orbitClosure_limit d_seq (Set.range c) hfin hgA i₀ x hx
  have hxorb : x ∈ orbitClosure c := Nivat.Colle.mem_orbitClosure_trans (hdorb i₀) hx
  have hyorb : y ∈ orbitClosure c := Nivat.Colle.mem_orbitClosure_trans (hdorb i₀) hy
  have heorb : ∀ i, e i ∈ orbitClosure c := fun i =>
    Nivat.Colle.mem_orbitClosure_trans (hdorb i) (mem_orbitClosure_of_joint_limit hjl i)
  -- step (i): `φx = φy`
  have hxy : act φ x = act φ y := by
    rw [hφ]
    exact act_eq_of_agree_halfPlane hp hnp hann hperp hxorb hyorb hagrZ
  -- equal `φ`-products across the family, then across the joint limit
  have hd_phi : ∀ i j, act φ (d_seq i) = act φ (d_seq j) := fun i j =>
    KM16.act_eq_of_jointSubseqLimit fam.equal_phi hjoint i j
  have he_phi : ∀ i j, act φ (e i) = act φ (e j) := fun i j =>
    act_eq_of_joint_limit hjl hd_phi i j
  -- Lemma 16(b), transported to the `e`
  have h16b : ∀ i j, i ≠ j → ∀ s : ℤ × ℤ, ∃ z ∈ B.image (· + s), d_seq i z ≠ d_seq j z :=
    fun i j hij s => KM16.distinct_configs_differ_on_translates hu h14 fam.in_orbit
      fam.distinct fam.equal_phi hjoint i j hij s
  have heB : ∀ i j, i ≠ j → ∀ s : ℤ × ℤ, ∃ z ∈ B.image (· + s), e i z ≠ e j z :=
    fun i j hij s => differ_of_joint_limit hjl h16b hij s
  have he_ne : ∀ i' j' : Fin fam.n, i' ≠ j' → e i' ≠ e j' := by
    intro i' j' hij'
    obtain ⟨z, -, hzne⟩ := heB i' j' hij' 0
    exact fun hcon => hzne (congrFun hcon z)
  -- `y` is distinct from every `e i`: translate `B` into the open half-plane
  have hyne : ∀ i, y ≠ e i := by
    intro i
    by_cases hi : i = i₀
    · subst hi; rw [he0]; exact Ne.symm hne
    · obtain ⟨s, hs⟩ := exists_translate_subset_halfPlane hp B
      obtain ⟨z, hz, hzne⟩ := heB i₀ i (Ne.symm hi) s
      intro heq
      exact hzne (by rw [he0, ← heq]; exact hagrHalf z (hs z hz))
  -- `e₁, …, e_n, y` is an `(n+1)`-element family, contradicting maximality
  set f : Fin (fam.n + 1) → Config ℤ := Fin.snoc e y with hf
  have hflast : f (Fin.last fam.n) = y := by rw [hf]; exact Fin.snoc_last _ _
  have hfcast : ∀ j, f j.castSucc = e j := by
    intro j; rw [hf]; exact Fin.snoc_castSucc _ _ _
  have hf_orbit : ∀ i, f i ∈ orbitClosure c := by
    intro i
    refine Fin.lastCases ?_ ?_ i
    · rw [hflast]; exact hyorb
    · intro j; rw [hfcast]; exact heorb j
  have hall : ∀ i, act φ (f i) = act φ y := by
    intro i
    refine Fin.lastCases ?_ ?_ i
    · rw [hflast]
    · intro j
      rw [hfcast, he_phi j i₀, he0, hxy]
  have hf_phi : ∀ i j, act φ (f i) = act φ (f j) := fun i j => (hall i).trans (hall j).symm
  have hf_distinct : ∀ i j, i ≠ j → f i ≠ f j := by
    refine Fin.lastCases ?_ ?_
    · refine Fin.lastCases ?_ ?_
      · intro hij; exact absurd rfl hij
      · intro j' _
        rw [hflast, hfcast]
        exact hyne j'
    · intro i'
      refine Fin.lastCases ?_ ?_
      · intro _
        rw [hfcast, hflast]
        exact Ne.symm (hyne i')
      · intro j' hij
        rw [hfcast, hfcast]
        exact he_ne i' j' fun h => hij (by rw [h])
  have hle := fam.maximal (fam.n + 1) f hf_orbit hf_distinct hf_phi
  omega

/-- **Kari–Moutot Lemma 17, two-sided form.**  In the situation of
`lemma17_of_maximal_family`, with `u` itself perpendicular to `v 0` (the situation Lemma 14
produces), the limit `d_seq i₀` is deterministic in *both* directions `u` and `−u`. -/
theorem lemma17_twoSided
    {c : Config ℤ} {u : ℤ × ℤ} {B : Finset (ℤ × ℤ)} {m : ℕ} {v : Fin (m + 1) → ℤ × ℤ}
    {φ : LaurentTwo ℤ} (hφ : φ = mono (v 0) - 1)
    (hfin : (Set.range c).Finite) (hu : u ≠ 0)
    (hnp : Pairwise fun i j => det (v i) (v j) ≠ 0)
    (hann : act (prodShift v) c = 0)
    (hperp : (v 0).1 * u.1 + (v 0).2 * u.2 = 0)
    (h14 : KM16.Lemma14HalfPlane c φ B u)
    (fam : MaximalPhiFamily c φ)
    {d_seq : Fin fam.n → Config ℤ}
    (hjoint : KM16.JointSubseqLimit fam.configs d_seq u)
    (i₀ : Fin fam.n) :
    toReal u ∉ ONED (d_seq i₀) ∧ toReal (-u) ∉ ONED (d_seq i₀) := by
  refine ⟨lemma17_of_maximal_family hφ hfin hu hnp hann h14 fam hjoint i₀ hu hperp, ?_⟩
  refine lemma17_of_maximal_family hφ hfin hu hnp hann h14 fam hjoint i₀ (neg_ne_zero.mpr hu) ?_
  show (v 0).1 * (-u).1 + (v 0).2 * (-u).2 = 0
  simp only [Prod.fst_neg, Prod.snd_neg, mul_neg]
  linarith [hperp]

/-- **Lemma 17 with its maximality hypothesis discharged.**  Corollary 15 costs *no new
hypotheses* at this call site: `exists_maximalPhiFamily_of_lemma14` consumes exactly the
`h14 : Lemma14HalfPlane c φ B u` that `lemma17_of_maximal_family` already assumes, plus
`hu` and `hfin`.  So the `fam` argument can be produced internally rather than demanded.

This closes step (a) of the three-step bridge from `lemma17_of_maximal_family` to `lemma17`
described in the docstring of `lemma17` below; steps (b) and (c) remain. -/
theorem lemma17_of_lemma14
    {c : Config ℤ} {u : ℤ × ℤ} {B : Finset (ℤ × ℤ)} {m : ℕ} {v : Fin (m + 1) → ℤ × ℤ}
    {φ : LaurentTwo ℤ} (hφ : φ = mono (v 0) - 1)
    (hfin : (Set.range c).Finite) (hu : u ≠ 0)
    (hnp : Pairwise fun i j => det (v i) (v j) ≠ 0)
    (hann : act (prodShift v) c = 0)
    (h14 : KM16.Lemma14HalfPlane c φ B u)
    {p : ℤ × ℤ} (hp : p ≠ 0) (hperp : (v 0).1 * p.1 + (v 0).2 * p.2 = 0) :
    ∃ fam : MaximalPhiFamily c φ, fam.n ≥ 1 ∧
      ∀ d_seq : Fin fam.n → Config ℤ, KM16.JointSubseqLimit fam.configs d_seq u →
        ∀ i₀ : Fin fam.n, toReal p ∉ ONED (d_seq i₀) := by
  obtain ⟨fam, hpos⟩ := exists_maximalPhiFamily_of_lemma14 hu hfin h14
  exact ⟨fam, hpos, fun d_seq hjoint i₀ =>
    lemma17_of_maximal_family hφ hfin hu hnp hann h14 fam hjoint i₀ hp hperp⟩

/-- **Non-vacuity of `lemma17_of_maximal_family`.**  Its hypothesis bundle is simultaneously
satisfiable, so the theorem is not proving something about an empty class of inputs.

Witness: `c = BL.const0`, `u = (1,0)`, `B = {(-1,0)}`, `v = ![(0,1), (1,0)]` (non-parallel,
with `v 0 = (0,1) ⟂ u`), `φ = T^{(0,1)} − 1`, `fam = constFamily φ` (so `n = 1`), and
`d_seq = (const0)`, which is a joint subsequential limit of itself.  The `Lemma14HalfPlane`
hypothesis is `KM16.lemma14HalfPlane_const0`. -/
theorem lemma17_hyps_satisfiable :
    ∃ (c : Config ℤ) (u : ℤ × ℤ) (B : Finset (ℤ × ℤ)) (v : Fin 2 → ℤ × ℤ)
      (φ : LaurentTwo ℤ) (fam : MaximalPhiFamily c φ) (d_seq : Fin fam.n → Config ℤ)
      (_i₀ : Fin fam.n),
      φ = mono (v 0) - 1 ∧ (Set.range c).Finite ∧ u ≠ 0 ∧
      (Pairwise fun i j => det (v i) (v j) ≠ 0) ∧
      act (prodShift v) c = 0 ∧
      (v 0).1 * u.1 + (v 0).2 * u.2 = 0 ∧
      KM16.Lemma14HalfPlane c φ B u ∧
      KM16.JointSubseqLimit fam.configs d_seq u ∧
      0 < fam.n := by
  classical
  refine ⟨BL.const0, ((1 : ℤ), (0 : ℤ)), {((-1 : ℤ), (0 : ℤ))},
    ![((0 : ℤ), (1 : ℤ)), ((1 : ℤ), (0 : ℤ))],
    mono ((0 : ℤ), (1 : ℤ)) - 1, constFamily _, fun _ => BL.const0, ⟨0, Nat.zero_lt_one⟩,
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Set.Finite.subset (Set.finite_singleton (0 : ℤ)) (by rintro _ ⟨z, rfl⟩; rfl)
  · intro h; simpa using congrArg Prod.fst h
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [det]
  · show act _ (fun _ => (0 : ℤ)) = 0
    exact act_zero_right _
  · norm_num
  · exact KM16.lemma14HalfPlane_const0 _
  · intro W M
    exact ⟨M, le_refl M, fun i w _ => rfl⟩
  · exact Nat.zero_lt_one

/- **Kari–Moutot Lemma 17** (the weaker statement formerly consumed by `KMProp18Assembly`).

**NOT PROVED, AND NOT THE PAPER'S STATEMENT.**  Two defects, both in the *signature*, are
catalogued in the Part 6 header below:

* the translation direction is reversed — the paper's `d = lim_j τ^{n_j u}(c)` lies in
  `subseqLimits c (-u)` under this development's `T`, and the direction is forced by the
  half-plane exhaustion in Lemma 16(b), not a matter of convention;
* even at the correct sign, `d` must be the `i₀`-th component of a *joint* limit of a
  **maximal** `φ`-family, which an arbitrary member of `subseqLimits c (-u)` is not.

So `lemma17_of_maximal_family` does not discharge it, and no repair short of restating it does.
Since 2026-09-14 **nothing depends on this declaration**: `Nivat.KM18A.kmProp18` is proved by
`Nivat.KM17.kmProp18` instead.  It is left in place, with its `sorry`, so that the record of
what was once assumed stays visible.

The earlier note on this docstring, kept for the record: deriving it would require (a)
Corollary 15 to produce the maximal family (`exists_maximalPhiFamily`, now **proved** — but note
that it needs `φ = T^v − 1` with `v ⟂ u`, data this signature does not carry, and that `φ ≠ 0` +
`act φ c = 0` alone is provably *not* enough: see `not_exists_maximalPhiFamily_of_annihilator`),
(b) the Lemma 14 choice of a `v 0` perpendicular to `u`, and (c) identifying the given
`d ∈ subseqLimits c u` with the `i₀`-th component of a *joint* limit of that family — the last
of which is false for an arbitrary `d`.

-/

/-! ## Part 6: Proposition 18, assembled along the paper's direction

### Why `lemma17` above is not the statement the paper proves

Two independent defects, both visible in its signature:

1. **Sign.**  Kari–Moutot's translation is `τ^t(c)_n = c_{n-t}` (p. 126), and the limit they take
   is `d_i = lim_j τ^{n_j u}(c_i)` (p. 137), i.e. `d_i n = lim_j c_i (n - n_j u)`.  In this
   development `T u f = fun z => f (z + u)` and `subseqLimits c u` collects the limits of
   `T^{n•u} c`, so the paper's `d_i` lies in `subseqLimits c_i (-u)`, **not** in
   `subseqLimits c_i u`.  The direction is not a convention one may flip: Lemma 16(b) needs the
   translated half-planes `H - n_j u - t` to exhaust `ℤ²`, and in Lean the same constraint shows
   up as `KM16.eq_of_agree_on_translated_box` demanding that the joint-limit direction coincide
   with the `Lemma14HalfPlane` direction.  `KM16.exists_lemma14HalfPlane_of_det` produces that
   direction as `-u` out of determinism at `u`; getting it as `+u` would need determinism at
   `-u`, which is exactly what fails in the one-sided case Proposition 18 is about.
2. **Arbitrary `d`.**  Even at the correct sign, the paper's `d` is the `i₀`-th component of a
   *joint* limit of a **maximal** family, not an arbitrary member of `subseqLimits c (-u)`.

Proposition 18 only asserts the *existence* of a good `d`, so neither defect blocks it.  The
theorem below proves `Nivat.KM.KMProp18` outright, with no `sorry` and no new axiom, by taking
the joint limit in the paper's direction. -/

/-- Reindexing the factors of a product annihilator by a transposition. -/
private theorem prodShift_swap {m : ℕ} (h : Fin (m + 1) → ℤ × ℤ) (i₀ : Fin (m + 1)) :
    (prodShift (fun i => h (Equiv.swap 0 i₀ i)) : LaurentTwo ℤ) = prodShift h := by
  classical
  show (∏ i, (mono (h (Equiv.swap 0 i₀ i)) - 1 : LaurentTwo ℤ)) = ∏ i, (mono (h i) - 1)
  exact Equiv.prod_comp (Equiv.swap 0 i₀) (fun i => (mono (h i) - 1 : LaurentTwo ℤ))

/-- **Kari–Moutot Proposition 18, with the perpendicular factor already selected.**

Given a non-parallel product annihilator `∏ᵢ (T^{vᵢ} − 1)` of `c` whose *first* factor direction
`v 0` is perpendicular to `u`, and given that `u` is a direction of determinism of `O(c)‾`, some
`d ∈ O(c)‾` is deterministic in **both** directions `±u`.

The witness is the `0`-th component of a joint subsequential limit, along `-u`, of a maximal
`φ`-family for `φ = T^{v 0} − 1`; that is the paper's `d = d₁`. -/
theorem kmProp18_of_perp {c : Config ℤ} (hfin : (Set.range c).Finite)
    {m : ℕ} {v : Fin (m + 1) → ℤ × ℤ} (hvne : v 0 ≠ 0)
    (hnp : Pairwise fun i j => det (v i) (v j) ≠ 0)
    (hann : act (prodShift v) c = 0)
    {u : ℤ × ℤ} (hu : u ≠ 0) (hperp : KM16.innerZ (v 0) u = 0)
    (hnotu : toReal u ∉ ONED c) :
    ∃ d ∈ orbitClosure c, toReal u ∉ ONED d ∧ -(toReal u) ∉ ONED d := by
  classical
  have hnegu : (-u : ℤ × ℤ) ≠ 0 := neg_ne_zero.mpr hu
  -- The Lemma 14 box, in the paper's direction `-u`.
  obtain ⟨B, -, -, h14⟩ :=
    KM16.exists_lemma14HalfPlane_of_det hfin hu hvne hperp rfl hnotu
  have hperpNeg : (v 0).1 * (-u : ℤ × ℤ).1 + (v 0).2 * (-u : ℤ × ℤ).2 = 0 := by
    have h0 : (v 0).1 * u.1 + (v 0).2 * u.2 = 0 := hperp
    simp only [Prod.fst_neg, Prod.snd_neg, mul_neg]
    linarith
  -- Corollary 15 + Lemma 17, both along `-u`.
  obtain ⟨fam, hfampos, hfam⟩ :=
    lemma17_of_lemma14 (v := v) (φ := mono (v 0) - 1) rfl hfin hnegu hnp hann h14 hnegu hperpNeg
  -- Lemma 16: a joint subsequential limit of the maximal family along `-u`.
  haveI hAfin : Finite ↥(Set.range c) := hfin.to_subtype
  obtain ⟨e, hjointA⟩ :=
    KM16.exists_jointSubseqLimit
      (fun (i : Fin fam.n) (z : ℤ × ℤ) =>
        (⟨fam.configs i z, KM16.mem_range_of_mem_orbitClosure (fam.in_orbit i) z⟩ :
          ↥(Set.range c)))
      (-u)
  have hjoint : KM16.JointSubseqLimit fam.configs (fun i z => (e i z).val) (-u) := by
    intro W M
    obtain ⟨k, hkM, hk⟩ := hjointA W M
    exact ⟨k, hkM, fun i w hw => congrArg Subtype.val (hk i w hw)⟩
  have hmem : (fun z => (e ⟨0, hfampos⟩ z).val) ∈ orbitClosure c :=
    Nivat.Colle.mem_orbitClosure_trans (fam.in_orbit ⟨0, hfampos⟩)
      (hjoint.mem_orbitClosure ⟨0, hfampos⟩)
  refine ⟨fun z => (e ⟨0, hfampos⟩ z).val, hmem, ?_, ?_⟩
  · exact fun hc => hnotu (Nivat.Colle.ONED_subset_of_mem_orbitClosure hmem hc)
  · rw [← Nivat.KM.toReal_neg]
    exact hfam _ hjoint ⟨0, hfampos⟩

/-- **Kari–Moutot Proposition 18**, proved.

`Nivat.KM.KMProp18` is the interface `Nivat.KM.kariMoutotTheorem4_of_prop18` consumes; this
theorem discharges it with no `sorry` and no new axiom.

Route: Kari–Szabados gives a pairwise non-parallel product annihilator `∏ᵢ (T^{hᵢ} − 1)` of `c`;
since `-u` is *not* a direction of determinism, Proposition 13
(`Nivat.Colle.exists_tangent_of_mem_ONED`) forces `-u ⟂ h i₀` for some `i₀`, hence `u ⟂ h i₀`;
transposing `i₀` to the front is the paper's *"without loss of generality we may assume
`i = 1`"*; then `kmProp18_of_perp`. -/
theorem kmProp18 : Nivat.KM.KMProp18 := by
  classical
  intro c hfin hann u hu hnotu hnegu
  obtain ⟨n, h, hnpos, hhne, hnp, hannp⟩ := kari_szabados_prodShift hfin hann
  obtain ⟨i₀, hi₀⟩ := Nivat.Colle.exists_tangent_of_mem_ONED hnp hannp hnegu
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hperpZ : KM16.innerZ (h i₀) u = 0 := by
    have hR : (((h i₀).1 * u.1 + (h i₀).2 * u.2 : ℤ) : ℝ) = 0 := by
      have hz := hi₀
      simp only [inner2, toReal, Prod.fst_neg, Prod.snd_neg] at hz
      push_cast
      linarith
    show (h i₀).1 * u.1 + (h i₀).2 * u.2 = 0
    exact_mod_cast hR
  refine kmProp18_of_perp hfin (v := fun i => h (Equiv.swap 0 i₀ i)) ?_ ?_ ?_ hu ?_ hnotu
  · simpa using hhne i₀
  · intro i j hij
    exact hnp fun hc => hij ((Equiv.swap 0 i₀).injective hc)
  · rw [prodShift_swap]; exact hannp
  · simpa using hperpZ

/-! ## Proved special cases -/

/-- **Monotonicity lemma**: ONED only shrinks along subsequential limits. -/
theorem ONED_subseqLimit_subset {c d : Config ℤ} {u : ℤ × ℤ}
    (hd : d ∈ subseqLimits c u) : ONED d ⊆ ONED c :=
  Nivat.Colle.ONED_subset_of_mem_orbitClosure
    (subseqLimits_subset_orbitClosure c u hd)

/-- **Lemma 17 under a transverse period hypothesis**: If c has a period p with
`⟨toReal (-u), p⟩ < 0`, then `toReal (-u) ∉ ONED d` for any subsequential limit d. -/
theorem lemma17_of_transverse_period {c d : Config ℤ} {u p : ℤ × ℤ}
    (hp : p ∈ Per c) (hd : d ∈ subseqLimits c u)
    (htrans : inner2 (toReal (-u)) p < 0) :
    toReal (-u) ∉ ONED d := by
  rintro ⟨hw, x, hx, y, hy, hne, hagr⟩
  have hpd : p ∈ Per d := mem_Per_of_mem_subseqLimits hd hp
  have hpx : p ∈ Per x := Nivat.Colle.mem_Per_of_mem_orbitClosure hpd hx
  have hpy : p ∈ Per y := Nivat.Colle.mem_Per_of_mem_orbitClosure hpd hy
  exact hne (Nivat.Colle.eq_of_agree_sideOf_of_mem_Per hpx hpy htrans hagr)

end Nivat.KM17
