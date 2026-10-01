/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.KariMoutot
import Nivat.SubseqLimit
import Nivat.External.Colle.KMLemma14
import Nivat.External.Colle.KMBox

/-!
# Kari–Moutot Lemma 16

**Kari–Moutot Lemma 16** (journal version, §4, p. 137), verbatim:

> "Let `d₁, …, dₙ` be defined as above.  Then (a) `φd₁ = ⋯ = φdₙ`, and
> (b) Configurations `dᵢ` are pairwise different on translated discrete boxes `B′ = B − t`
> for all `t ∈ ℤ²`."

Source: J. Kari, E. Moutot, *Decidability and Periodicity of Low Complexity Tilings*,
Theory of Computing Systems **67** (2023) 125–148, doi `10.1007/s00224-021-10063-8`,
Lemma 16 (p. 137).

## What "defined as above" actually says, and why it matters

The sentence the lemma refers to is the paragraph immediately preceding it (p. 137, verbatim):

> "Let `c₁, …, cₙ ∈ X` be pairwise distinct such that `φc₁ = ⋯ = φcₙ`, with `n` as large as
> possible.  By Corollary 15 such a maximal `n` exists.  Let us repeatedly translate the
> configurations `cᵢ` by `τ^u` and take a limit: by compactness there exists
> `n₁ < n₂ < n₃ …` such that `dᵢ = lim_{j→∞} τ^{nⱼ u}(cᵢ)` exists for all `i ∈ {1, …, n}`."

Two features of this setup are load-bearing for part (b), and **neither is maximality**:

1. **One common sequence of times.**  There is a *single* sequence `n₁ < n₂ < ⋯` along which
   *all* `n` limits are taken simultaneously ("exists for all `i`").  This is
   `JointSubseqLimit` below.  The weaker `∀ i, dᵢ ∈ subseqLimits cᵢ u` — each `i` free to pick
   its own times — is **not** enough, and was the mathematical error in the previous version of
   this file (see "History" below).
2. **`φcᵢ = φcⱼ`, not `φcᵢ = 0`.**  In §4 the annihilator of `c` is the *product*
   `φ₁ ⋯ φ_m` and `φ = φ₁` is only its first factor; `φ` does **not** annihilate the `cᵢ`.
   So the honest hypothesis is `hc_ann_eq`, and part (a) is a real statement rather than
   `0 = 0`.

Maximality of `n` (Corollary 15) is what Lemma **17** consumes, to manufacture a contradiction
from `n + 1` configurations.  Lemma 16 itself never uses it.

## The verbatim proof of part (b), and its formal counterpart

Kari–Moutot, p. 137, verbatim:

> "(b) Let `B′ = B − t` for some `t ∈ ℤ²`.  Suppose `d_{i₁}|_{B′} = d_{i₂}|_{B′}`.  By the
> definition of convergence, for all sufficiently large `j` we have
> `τ^{nⱼu}(c_{i₁})|_{B′} = τ^{nⱼu}(c_{i₂})|_{B′}`.  This is equivalent to
> `τ^{nⱼu+t}(c_{i₁})|_B = τ^{nⱼu+t}(c_{i₂})|_B`.  By Lemma 14 then also
> `τ^{nⱼu+t}(c_{i₁})|_H = τ^{nⱼu+t}(c_{i₂})|_H` where `H = H_{−u}`.  This means that for all
> sufficiently large `j` the configurations `c_{i₁}` and `c_{i₂}` are identical on the domain
> `H − nⱼu − t`.  But these domains cover the whole `ℤ²` as `j ⟶ ∞` so that `c_{i₁} = c_{i₂}`,
> a contradiction."

So the contradiction is with **`c_{i₁} ≠ c_{i₂}`** — the pairwise distinctness of the `cᵢ`,
which is part of the given data.  It is *not* with `d_{i₁} ≠ d_{i₂}`.  That is exactly why
`hd_distinct` is derivable rather than assumable, and the whole content of this file's repair:
`eq_of_agree_on_translated_box` is the displayed argument, and `hd_distinct` falls out of it as
the corollary `distinct_of_jointSubseqLimit`.

The two inputs the argument needs, beyond the data, are

* the **joint** limit (feature 1 above) — `JointSubseqLimit`, whose existence by compactness is
  proved here (`exists_jointSubseqLimit`), so it is not an assumption smuggled in; and
* **Lemma 14 in its half-plane form** (p. 136, verbatim): *"For any `d, e ∈ X` such that
  `φd = φe` holds: `d|_B = e|_B ⟹ d|_H = e|_H`."* — `Lemma14HalfPlane` below.

### Translation convention, and the sign of the half plane

`Nivat.T v g z = g (z + v)` and `Nivat.subseqLimits G u` is built from `w ↦ G (w + n • u)`, i.e.
Lean's `T v` is Kari–Moutot's `τ^{−v}`.  `halfPlane u = {z | ⟨z, u⟩ < 0}` below is Kari–Moutot's
`H_u`, and `halfPlane (-u)` is their `H_{−u}`, which is the `H` of Lemma 14.  The exhaustion
"these domains cover the whole `ℤ²`" becomes: for fixed `w`, `w − t − m • u ∈ halfPlane u` for
all large `m`, because `⟨u, u⟩ > 0`; that is why `lemma16` is stated for a general direction and
gets applied at whichever sign the caller's Lemma 14 produced.

**The window and the conclusion sit on opposite sides.**  Kari–Moutot's box `B = B_u^k` lies in
`{x | −k < ⟨x,u⟩ < 0} ⊆ H_u` and their Lemma 14 concludes on `H = H_{−u}`; the window determines
cell `0` from cells *below* it in `⟨·, u⟩`, so agreement propagates upwards and the two half
planes cannot be the same one.  Accordingly `lemma14HalfPlane_of_stripe_and_window` below proves
`Lemma14HalfPlane c φ B (-u)` with `B ⊆ halfPlane u`.  An earlier version of this docstring
asserted that `halfPlane u` is at once the side of `Nivat.KMBox.exists_window_of_det`'s window
and the side of the conclusion; that was wrong, and the sign is now fixed in the statements
rather than in prose.

## History: two successive wrong statements, both now retired

* **2026-09-12 and earlier.**  `distinct_configs_differ_on_translates` was an `axiom`, and
  `#print axioms` confirmed it entailed `False`: `B` was quantified outermost and could be
  instantiated at `∅`, making the conclusion `∃ z ∈ (∅ : Finset _).image _, …` false outright.
  Machine-checked in `scratch/lead_check_axioms.lean` (`LeadCheck.km16_conclusion_is_false`).
* **2026-09-13, the "repair".**  Hypotheses `B.Nonempty` and `d₁ ≠ d₂` were added and the
  `axiom` became a `sorry`.  **That statement is still false**, because it still relates `B` to
  nothing: take `u = (1,0)`, `c z = if z.1 < 0 then 0 else z.1 % 2`, `c₁ = 0` and
  `c₂ = (z ↦ z.1 % 2)` (both in `orbitClosure c`, `c₁ ≠ c₂`), `d₁ = c₁ ∈ subseqLimits c₁ u`,
  `d₂ = c₂ ∈ subseqLimits c₂ u` (times `n` even), `d₁ ≠ d₂`, `B = {(0,0)}` nonempty — and at
  `t = 0` the only point of `B.image (· + t)` is `(0,0)`, where `d₁ (0,0) = 0 = d₂ (0,0)`.  The
  missing ingredient was never `d₁ ≠ d₂`; it is the pair (joint times, Lemma 14 for *this* `B`),
  and those are what the present version takes.

## Status

`lemma16` is **proved outright, parts (a) and (b), no `sorry` and no new `axiom`**, from
`Lemma14HalfPlane` and `JointSubseqLimit`.  `hd_distinct` is **gone** from the hypotheses: it is
now the derived `distinct_of_jointSubseqLimit`.  So is `B.Nonempty`.

`Lemma14HalfPlane` is a hypothesis of `lemma16`, not an assumption about Lemma 16: it *is*
Kari–Moutot Lemma 14 (p. 136).  As of this version it is also a **theorem**:
`exists_lemma14HalfPlane_of_det` proves it outright from the data of Kari–Moutot §4 — `c` of
finite range, `u` a direction of determinism of `O(c)‾`, and `φ = x^v − 1` the factor of the
annihilator whose `v` is perpendicular to `u` — by gluing `Nivat.KM14.lemma14_stripe` (the
periodicity half) to the determinism window of §2.2 (the compactness half) through the specific
rectangle `B_u^k`, which is reconstructed here as `kmBox`.  The `[Finite α]` of
`Nivat.KMBox.exists_window_of_det` is traded for `(Set.range c).Finite` by
`exists_window_of_det_of_finite_range`.  See the section "Gluing `lemma14_stripe` and the
determinism window" for the sign convention, which differs from what this docstring used to
claim.
-/

namespace Nivat.KM16

open Nivat

/-! ### Kari–Moutot's discrete half plane -/

/-- Kari–Moutot §2.2 (p. 130), verbatim: *"For a nonzero vector `u ∈ ℤ² ∖ {0}` we denote
`H_u = {x ∈ ℤ² | ⟨x, u⟩ < 0}` for the discrete half plane in direction `u`."*

Spelled with the integer pairing rather than `Nivat.inner2`, because the proof of part (b) does
integer arithmetic with it; `mem_halfPlane_iff_inner2` is the bridge to the real-valued `inner2`
used by `Nivat.ONED` and by `Nivat.KMBox.exists_window_of_det`.

Non-degeneracy: this is a genuine constraint on `z`, with witnesses on both sides — for
`u = (1,0)`, `(-1,0) ∈ halfPlane u` and `(1,0) ∉ halfPlane u`
(`neg_mem_halfPlane_self`, `not_mem_halfPlane_self`). -/
def halfPlane (u : ℤ × ℤ) : Set (ℤ × ℤ) := {z | z.1 * u.1 + z.2 * u.2 < 0}

theorem mem_halfPlane_iff (u z : ℤ × ℤ) : z ∈ halfPlane u ↔ z.1 * u.1 + z.2 * u.2 < 0 := Iff.rfl

/-- `halfPlane u` is `{z | inner2 (toReal u) z < 0}`: the integer spelling above and the real
spelling used by `Nivat.ONED` and `Nivat.KMBox.exists_window_of_det` define the same set. -/
theorem mem_halfPlane_iff_inner2 (u z : ℤ × ℤ) :
    z ∈ halfPlane u ↔ inner2 (toReal u) z < 0 := by
  rw [mem_halfPlane_iff]
  show _ ↔ (z.1 : ℝ) * (u.1 : ℝ) + (z.2 : ℝ) * (u.2 : ℝ) < 0
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

/-- `0 < ⟨u, u⟩` for `u ≠ 0`.  Extracted because the exhaustion argument of part (b) is exactly
"`m * ⟨u, u⟩` beats any fixed integer". -/
theorem inner_self_pos {u : ℤ × ℤ} (hu : u ≠ 0) : 0 < u.1 * u.1 + u.2 * u.2 := by
  have hor : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hu (Prod.ext hc.1 hc.2)
  rcases hor with h | h
  · have h2 : 0 < u.1 * u.1 := mul_self_pos.mpr h
    nlinarith [mul_self_nonneg u.2]
  · have h2 : 0 < u.2 * u.2 := mul_self_pos.mpr h
    nlinarith [mul_self_nonneg u.1]

/-- `halfPlane` is inhabited whenever `u ≠ 0`: `-u` itself lies in it.  A non-vacuity check on
`halfPlane`, and the fact the arithmetic of part (b) rests on (`0 < ⟨u, u⟩`). -/
theorem neg_mem_halfPlane {u : ℤ × ℤ} (hu : u ≠ 0) : -u ∈ halfPlane u := by
  rw [mem_halfPlane_iff]
  have h := inner_self_pos hu
  show (-u).1 * u.1 + (-u).2 * u.2 < 0
  simp only [Prod.fst_neg, Prod.snd_neg]
  nlinarith

/-- `halfPlane u` is a proper subset: `u ∉ halfPlane u` for `u ≠ 0`.  Together with
`neg_mem_halfPlane` this rules out both degeneracies (`∅` and `univ`). -/
theorem not_mem_halfPlane {u : ℤ × ℤ} (hu : u ≠ 0) : u ∉ halfPlane u := by
  rw [mem_halfPlane_iff]
  have h := inner_self_pos hu
  omega

/-! ### Joint subsequential limits: "exists for all `i`" -/

/-- **A family of subsequential limits taken along one common sequence of times.**

Kari–Moutot, p. 137, verbatim: *"by compactness there exists `n₁ < n₂ < n₃ …` such that
`dᵢ = lim_{j→∞} τ^{nⱼ u}(cᵢ)` exists for all `i ∈ {1, …, n}`."*  The quantifier order is the
point: **one** sequence `nⱼ`, **all** `i`.

`JointSubseqLimit c_seq d_seq u` says: for every finite window `W` and every bound `M` there is
a single time `m ≥ M` at which *every* `d_seq i` agrees with `T^{m • u} (c_seq i)` on `W`.
Compare `Nivat.subseqLimits`, which is the `n = 1` case; `JointSubseqLimit.mem_subseqLimits`
shows this is strictly stronger than `∀ i, d_seq i ∈ subseqLimits (c_seq i) u`, which lets each
`i` choose its own times and is *not* what the paper constructs.

Non-vacuous: `exists_jointSubseqLimit` produces one for every `c_seq` over a finite alphabet,
by the same compactness the paper invokes. -/
def JointSubseqLimit {α : Type*} {n : ℕ} (c_seq d_seq : Fin n → Config α) (u : ℤ × ℤ) : Prop :=
  ∀ (W : Finset (ℤ × ℤ)) (M : ℕ), ∃ m : ℕ, M ≤ m ∧
    ∀ (i : Fin n), ∀ w ∈ W, d_seq i w = c_seq i (w + (m : ℤ) • u)

/-- A joint limit is in particular a limit for each index separately. -/
theorem JointSubseqLimit.mem_subseqLimits {α : Type*} {n : ℕ} {c_seq d_seq : Fin n → Config α}
    {u : ℤ × ℤ} (h : JointSubseqLimit c_seq d_seq u) (i : Fin n) :
    d_seq i ∈ subseqLimits (c_seq i) u := by
  intro W M
  obtain ⟨m, hmM, hm⟩ := h W M
  exact ⟨m, hmM, hm i⟩

/-- Each member of a joint limit lies in the orbit closure of its source. -/
theorem JointSubseqLimit.mem_orbitClosure {α : Type*} {n : ℕ} {c_seq d_seq : Fin n → Config α}
    {u : ℤ × ℤ} (h : JointSubseqLimit c_seq d_seq u) (i : Fin n) :
    d_seq i ∈ orbitClosure (c_seq i) :=
  subseqLimits_subset_orbitClosure _ u (h.mem_subseqLimits i)

/-- **Compactness, in the joint form the paper uses.**  Over a finite alphabet, any finite
family `c_seq : Fin n → Config α` of configurations admits a family of subsequential limits
along `u` taken at *one common* sequence of times.

This is Kari–Moutot's *"by compactness there exists `n₁ < n₂ < n₃ …` such that
`dᵢ = lim_{j→∞} τ^{nⱼ u}(cᵢ)` exists for all `i`"* (p. 137).  It is what makes
`JointSubseqLimit` a description of an existing object rather than an extra assumption.

Proof as in `Nivat.subseqLimits_nonempty` and `Nivat.KMBox.exists_pair_limit`, run on the finite
type `Fin n → α`: for each cell `w` the pushforward of an ultrafilter refining `atTop` along
`m ↦ (i ↦ c_seq i (w + m • u))` is principal, and its value is the joint limit at `w`. -/
theorem exists_jointSubseqLimit {α : Type*} [Finite α] {n : ℕ} (c_seq : Fin n → Config α)
    (u : ℤ × ℤ) : ∃ d_seq : Fin n → Config α, JointSubseqLimit c_seq d_seq u := by
  classical
  set 𝔲 : Ultrafilter ℕ := Ultrafilter.of Filter.atTop with h𝔲
  have key : ∀ w : ℤ × ℤ, ∃ p : Fin n → α,
      {m : ℕ | (fun i => c_seq i (w + (m : ℤ) • u)) = p} ∈ 𝔲 := by
    intro w
    obtain ⟨p, hp⟩ := Ultrafilter.eq_pure_of_finite
      (Ultrafilter.map (fun m : ℕ => (fun i => c_seq i (w + (m : ℤ) • u))) 𝔲)
    refine ⟨p, ?_⟩
    have hmem : ({p} : Set (Fin n → α)) ∈
        Ultrafilter.map (fun m : ℕ => (fun i => c_seq i (w + (m : ℤ) • u))) 𝔲 := by
      rw [hp]; exact Ultrafilter.mem_pure.mpr rfl
    rwa [Ultrafilter.mem_map] at hmem
  choose y hy using key
  refine ⟨fun i w => y w i, ?_⟩
  intro W M
  have h1 : {m : ℕ | M ≤ m} ∈ 𝔲 := Ultrafilter.of_le Filter.atTop (Filter.mem_atTop M)
  have h2 : (⋂ w ∈ W, {m : ℕ | (fun i => c_seq i (w + (m : ℤ) • u)) = y w}) ∈ 𝔲 :=
    (Filter.biInter_finset_mem W).mpr fun w _ => hy w
  obtain ⟨m, hm⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem h1 h2)
  refine ⟨m, hm.1, fun i w hw => ?_⟩
  have hm2 := hm.2
  simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hm2
  exact (congrFun (hm2 w hw) i).symm

/-! ### Kari–Moutot Lemma 14, in the half-plane form Lemma 16(b) consumes -/

/-- **Kari–Moutot Lemma 14** (p. 136), verbatim: *"For any `d, e ∈ X` such that `φd = φe` holds:
`d|_B = e|_B ⟹ d|_H = e|_H`."*

Here `X = orbitClosure c`.  The predicate is stated for a general direction: `Lemma14HalfPlane
c φ B u` concludes on `halfPlane u`, and Kari–Moutot's own instance is the one with the box in
`halfPlane u` and the conclusion on `halfPlane (-u)`, i.e. `Lemma14HalfPlane c φ B (-u)` — see
the sign discussion in the module docstring and in the gluing section below.

**This is Kari–Moutot's Lemma 14 verbatim, not a convenience hypothesis.**  It is what the `B`
of §4 exists in order to satisfy: Kari–Moutot obtain `B = B_u^k` from the compactness statement
of §2.2 (*"the contents of a configuration in the discrete box `B_u^k` are enough to uniquely
determine the contents in cell `0`"*, their property (2)), and Lemma 14 is proved from (2)
together with the `v`-periodicity of `d − e`.

Status in this development: **proved**, by `exists_lemma14HalfPlane_of_det` below (and, with the
window supplied by the caller, by `lemma14HalfPlane_of_stripe_and_window`).  Its two halves are

* `Nivat.KM14.lemma14_stripe`, the periodicity transport: agreement propagates from `B` to the
  stripe `S = ⋃_i (B + i v)`;
* the §2.2 compactness statement producing a finite window inside the open half plane that
  determines cell `0` — `Nivat.KMBox.exists_window_of_det`, restated for finite-range
  configurations over `ℤ` as `exists_window_of_det_of_finite_range`.

Gluing them is Kari–Moutot's sentence *"Applying (2) on suitable translates of `d` and `e`
allows us to conclude that `d|_H = e|_H`"*, and it needs the **specific rectangle**
`B_u^k = {x | −k < ⟨x, u⟩ < 0 ∧ −k < ⟨x, ũ⟩ < k}` with `k > |⟨v, ũ⟩|` rather than an arbitrary
finite window, because the identity `⋃_{i∈ℤ}(B_u^k + iv) = {x | −k < ⟨x,u⟩ < 0}` (p. 136) is what
makes the stripe a full slab.  `Nivat.KMBox.exists_window_of_det` deliberately discards the
shape of `B`, so `kmBox` rebuilds the rectangle and `exists_kmBox_window` re-derives property (2)
for it by enlarging `k`.

Non-degeneracy: the conclusion is `∀ z ∈ halfPlane u, d z = e z` with `halfPlane u` a fixed
proper nonempty subset of `ℤ²` (`neg_mem_halfPlane`, `not_mem_halfPlane`) — not an
`∃ t`-guarded predicate that would hold of every `z`. -/
def Lemma14HalfPlane (c : Config ℤ) (φ : LaurentTwo ℤ) (B : Finset (ℤ × ℤ)) (u : ℤ × ℤ) : Prop :=
  ∀ d ∈ orbitClosure c, ∀ e ∈ orbitClosure c, act φ d = act φ e →
    (∀ z ∈ B, d z = e z) → ∀ z ∈ halfPlane u, d z = e z

/-- **`Lemma14HalfPlane` is refutable**, hence not a vacuous hypothesis.

This is the anti-cheat check on the one premise `lemma16` gained.  A hypothesis that happened to
be true for every instantiation would make the proof of part (b) hollow — it would be the "add a
premise that secretly implies the conclusion" failure mode.  It is not: at `c = Nivat.KM.vline`,
`φ = 0`, `B = ∅`, `u = (1,0)`, the translate `T (5,0) vline` and the all-zero configuration are
both in `orbitClosure vline` and have the same (zero) `φ`-product, yet differ at `(-5, 0)`, which
lies in `halfPlane (1,0) = {z | z.1 < 0}`.

This is the cheapest refutation rather than an interesting one — `φ = 0` and `B = ∅` make both
antecedents free — so it shows only that the predicate has genuine content, not that the
`B = B_u^k` instance Kari–Moutot need is hard.  That instance is the subject of the note above. -/
theorem not_lemma14HalfPlane_vline :
    ¬ Lemma14HalfPlane KM.vline 0 ∅ ((1 : ℤ), (0 : ℤ)) := by
  intro h
  have hz : ((-5 : ℤ), (0 : ℤ)) ∈ halfPlane ((1 : ℤ), (0 : ℤ)) := by
    rw [mem_halfPlane_iff]; norm_num
  have hd : T ((5 : ℤ), (0 : ℤ)) KM.vline ∈ orbitClosure KM.vline :=
    T_mem_of_mem_orbitClosure (self_mem_orbitClosure KM.vline) _
  have := h _ hd _ KM.const0_mem_orbitClosure_vline
    (by rw [act_zero_left, act_zero_left]) (fun z hz => absurd hz (Finset.notMem_empty z))
    _ hz
  -- `T (5,0) vline (-5,0) = vline (0,0) = 1`, while `const0 (-5,0) = 0`.
  rw [show T ((5 : ℤ), (0 : ℤ)) KM.vline ((-5 : ℤ), (0 : ℤ)) = 1 from by
    show KM.vline (((-5 : ℤ), (0 : ℤ)) + ((5 : ℤ), (0 : ℤ))) = 1
    norm_num [KM.vline]] at this
  exact absurd this (by norm_num [BL.const0])

/-- **`Lemma14HalfPlane` is satisfiable**, non-vacuously, with a nonempty `B`.

The other half of the anti-cheat check on the premise: `not_lemma14HalfPlane_vline` shows it is
not always true, and this shows it is not always false, so `lemma16` is not proving something
about an empty class of inputs.

Witness: `c = Nivat.BL.const0`, whose orbit closure is the single configuration `const0`
(everything in it agrees with a translate of `const0` on every window, hence is `0` everywhere),
so the conclusion holds because `d = e`.  The box is `B = {(-1, 0)}`, a nonempty subset of
`halfPlane (1,0)`, exactly as `Nivat.KMBox.exists_window_of_det` would deliver it. -/
theorem lemma14HalfPlane_const0 (φ : LaurentTwo ℤ) :
    Lemma14HalfPlane BL.const0 φ {((-1 : ℤ), (0 : ℤ))} ((1 : ℤ), (0 : ℤ)) := by
  have hall : ∀ x ∈ orbitClosure BL.const0, x = BL.const0 := by
    intro x hx
    funext z
    obtain ⟨v, hv⟩ := hx {z}
    exact hv z (Finset.mem_singleton_self z)
  intro d hd e he _ _ z _
  rw [hall d hd, hall e he]

/-! ### Gluing `lemma14_stripe` and the determinism window

This section proves `Lemma14HalfPlane` outright, from the hypotheses Kari–Moutot's §4 supplies:
`c` has finite range, `u` is a direction of determinism of `O(c)‾`, and `φ = x^{v} − 1` is the
factor of the annihilator whose direction `v` is **perpendicular** to `u`.

### The sign, spelled out once

Kari–Moutot's §4 is set up like this (p. 136, verbatim): *"Let `k` be such that the contents of
the discrete box `B = B_u^k` determine the content of cell `0`, that is, for `d, e ∈ X`
`d|_B = e|_B ⟹ d_0 = e_0`. … We can choose `k` so that `k > |⟨ũ, v⟩|`.  To shorten notations,
let us also denote `H = H_{−u}`."*  So the box `B_u^k ⊆ {x | −k < ⟨x,u⟩ < 0} = H_u` and the
conclusion `d|_H = e|_H` of Lemma 14 live on **opposite** sides: the window is in `H_u`, the
conclusion in `H_{−u}`.  That is forced — the window determines cell `0` from cells *below* it in
`⟨·, u⟩`, so information travels upwards, from `H_u` towards `H_{−u}`, and the induction that
Kari–Moutot compress into *"Applying (2) on suitable translates of `d` and `e`"* runs in that
direction only.

Hence the conclusion below is `Lemma14HalfPlane c φ B (-u)`, with `B ⊆ halfPlane u`.  The module
docstring's remark that the window sits on the same side as the conclusion half plane is a slip;
`halfPlane u` and `halfPlane (-u)` are the two sides, and both appear here, one for the window and
one for the conclusion.  Nothing downstream is affected: `lemma16` quantifies over `u`, and is
applied at `-u`.

### The three steps

1. `kmBox u k` is Kari–Moutot's rectangle `B_u^k = {x | −k < ⟨x,u⟩ < 0 ∧ −k < ⟨x,ũ⟩ < k}`
   (`ũ = Nivat.KM.perpOf u`), a genuine `Finset` because `x ↦ (⟨x,u⟩, ⟨x,ũ⟩)` is injective for
   `u ≠ 0`.
2. `exists_mem_kmBox_of_stripe` is the covering `{x | −k < ⟨x,u⟩ < 0} ⊆ ⋃_j (B_u^k + jv)`, which
   is where `⟨u,v⟩ = 0` and `k > |⟨v,ũ⟩|` are used: perpendicularity keeps `⟨·,u⟩` fixed along
   `v`, and `k > |⟨v,ũ⟩|` makes consecutive translates overlap in the `ũ` coordinate.  This is
   Kari–Moutot's displayed identity `S = ⋃_{i∈ℤ}(B + iv) = {x | −k < ⟨x,u⟩ < 0}` (p. 136).
3. `lemma14HalfPlane_of_stripe_and_window` glues: `KM14.lemma14_stripe` gives agreement on `S`,
   and then an induction on `⟨w,u⟩` upwards, each step applying the window at the translate `w`,
   gives agreement on everything with `⟨w,u⟩ > −k`, in particular on `halfPlane (-u)`.

`exists_kmBox_window` supplies the window hypothesis from determinism alone, and
`exists_lemma14HalfPlane_of_det` is the fully discharged statement.  The `[Finite α]` of
`Nivat.KMBox.exists_window_of_det` is replaced by `(Set.range c).Finite` there: the ultrafilter
argument only ever needs the values, which lie in `Set.range c` for every member of the orbit
closure (`mem_range_of_mem_orbitClosure`). -/

/-- The integer pairing `⟨z, u⟩`, the same expression `halfPlane` is defined by
(`mem_halfPlane_iff_innerZ`).  Kept as a `def` rather than unfolded so that `omega` treats it as
an atom in the arithmetic below. -/
def innerZ (z u : ℤ × ℤ) : ℤ := z.1 * u.1 + z.2 * u.2

theorem mem_halfPlane_iff_innerZ (u z : ℤ × ℤ) : z ∈ halfPlane u ↔ innerZ z u < 0 := Iff.rfl

theorem innerZ_add (z₁ z₂ u : ℤ × ℤ) : innerZ (z₁ + z₂) u = innerZ z₁ u + innerZ z₂ u := by
  simp only [innerZ, Prod.fst_add, Prod.snd_add]; ring

theorem innerZ_sub (z₁ z₂ u : ℤ × ℤ) : innerZ (z₁ - z₂) u = innerZ z₁ u - innerZ z₂ u := by
  simp only [innerZ, Prod.fst_sub, Prod.snd_sub]; ring

theorem innerZ_zsmul (j : ℤ) (z u : ℤ × ℤ) : innerZ (j • z) u = j * innerZ z u := by
  simp only [innerZ, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- **`u` and `ũ` together separate the lattice**: for `u ≠ 0` a nonzero `v` perpendicular to `u`
has `⟨v, ũ⟩ ≠ 0`.  This is what makes the period `v` move along the stripe rather than stand
still. -/
theorem innerZ_perp_ne_zero {u v : ℤ × ℤ} (hu : u ≠ 0) (hv : v ≠ 0) (hperp : innerZ v u = 0) :
    innerZ v (KM.perpOf u) ≠ 0 := by
  intro hb
  have hn : 0 < u.1 * u.1 + u.2 * u.2 := inner_self_pos hu
  have ha : v.1 * u.1 + v.2 * u.2 = 0 := hperp
  have hb' : v.1 * -u.2 + v.2 * u.1 = 0 := by
    simpa only [innerZ, KM.perpOf] using hb
  have h1 : (u.1 * u.1 + u.2 * u.2) * v.1 = 0 := by linear_combination u.1 * ha - u.2 * hb'
  have h2 : (u.1 * u.1 + u.2 * u.2) * v.2 = 0 := by linear_combination u.2 * ha + u.1 * hb'
  refine hv (Prod.ext ?_ ?_)
  · exact (mul_eq_zero.mp h1).resolve_left hn.ne'
  · exact (mul_eq_zero.mp h2).resolve_left hn.ne'

/-! #### The discrete box `B_u^k` -/

/-- Kari–Moutot's discrete box (§2.2, p. 131, verbatim):
`B_u^k = {x ∈ ℤ² | −k < ⟨x, u⟩ < 0 and −k < ⟨x, ũ⟩ < k}`, as a set. -/
def kmBoxSet (u : ℤ × ℤ) (k : ℤ) : Set (ℤ × ℤ) :=
  {x | -k < innerZ x u ∧ innerZ x u < 0 ∧
    -k < innerZ x (KM.perpOf u) ∧ innerZ x (KM.perpOf u) < k}

/-- `B_u^k` is finite: `x ↦ (⟨x,u⟩, ⟨x,ũ⟩)` is injective for `u ≠ 0` (it is `⟨u,u⟩` times the
identity in disguise), and the box is the preimage of a bounded rectangle of pairs. -/
theorem kmBoxSet_finite {u : ℤ × ℤ} (hu : u ≠ 0) (k : ℤ) : (kmBoxSet u k).Finite := by
  have hn : 0 < u.1 * u.1 + u.2 * u.2 := inner_self_pos hu
  have hinj : Function.Injective (fun x : ℤ × ℤ => (innerZ x u, innerZ x (KM.perpOf u))) := by
    intro x y hxy
    have h1 : x.1 * u.1 + x.2 * u.2 = y.1 * u.1 + y.2 * u.2 := congrArg Prod.fst hxy
    have h2 : x.1 * -u.2 + x.2 * u.1 = y.1 * -u.2 + y.2 * u.1 := by
      simpa only [innerZ, KM.perpOf] using congrArg Prod.snd hxy
    have e1 : (u.1 * u.1 + u.2 * u.2) * (x.1 - y.1) = 0 := by
      linear_combination u.1 * h1 - u.2 * h2
    have e2 : (u.1 * u.1 + u.2 * u.2) * (x.2 - y.2) = 0 := by
      linear_combination u.2 * h1 + u.1 * h2
    refine Prod.ext ?_ ?_
    · have := (mul_eq_zero.mp e1).resolve_left hn.ne'
      linarith
    · have := (mul_eq_zero.mp e2).resolve_left hn.ne'
      linarith
  have hpre : kmBoxSet u k
      = (fun x : ℤ × ℤ => (innerZ x u, innerZ x (KM.perpOf u))) ⁻¹'
        (Set.Ioo (-k) 0 ×ˢ Set.Ioo (-k) k) := by
    ext x
    simp only [kmBoxSet, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, Set.mem_Ioo]
    tauto
  rw [hpre]
  exact Set.Finite.preimage (fun a _ b _ h => hinj h)
    ((Set.finite_Ioo _ _).prod (Set.finite_Ioo _ _))

/-- Kari–Moutot's discrete box `B_u^k` as a `Finset` (empty at the degenerate `u = 0`, which no
statement below uses). -/
noncomputable def kmBox (u : ℤ × ℤ) (k : ℤ) : Finset (ℤ × ℤ) :=
  if h : u = 0 then ∅ else (kmBoxSet_finite h k).toFinset

theorem mem_kmBox {u : ℤ × ℤ} (hu : u ≠ 0) (k : ℤ) (x : ℤ × ℤ) :
    x ∈ kmBox u k ↔ -k < innerZ x u ∧ innerZ x u < 0 ∧
      -k < innerZ x (KM.perpOf u) ∧ innerZ x (KM.perpOf u) < k := by
  rw [kmBox, dif_neg hu, Set.Finite.mem_toFinset]
  rfl

/-- `B_u^k` sits inside the open half plane `H_u`, as Kari–Moutot's `−k < ⟨x,u⟩ < 0` says. -/
theorem kmBox_subset_halfPlane {u : ℤ × ℤ} (hu : u ≠ 0) (k : ℤ) :
    ∀ z ∈ kmBox u k, z ∈ halfPlane u := by
  intro z hz
  rw [mem_kmBox hu] at hz
  exact hz.2.1

/-- `B_u^k` is nonempty as soon as `k > ⟨u,u⟩`: it contains `−u`. -/
theorem neg_mem_kmBox {u : ℤ × ℤ} (hu : u ≠ 0) {k : ℤ} (hk : innerZ u u < k) :
    -u ∈ kmBox u k := by
  have h2 : 0 < innerZ u u := inner_self_pos hu
  have h0 : innerZ (-u) u = -innerZ u u := by
    simp only [innerZ, Prod.fst_neg, Prod.snd_neg]; ring
  have h1 : innerZ (-u) (KM.perpOf u) = 0 := by
    simp only [innerZ, KM.perpOf, Prod.fst_neg, Prod.snd_neg]; ring
  rw [mem_kmBox hu]
  omega

/-! #### The stripe: `⋃_{i ∈ ℤ} (B_u^k + i v) = {x | −k < ⟨x,u⟩ < 0}` -/

/-- **The covering step**, Kari–Moutot p. 136, verbatim: *"this periodicity transmits values `0`
from the region `B` to the stripe `S = ⋃_{i∈ℤ}(B + iv) = {x ∈ ℤ² | −k < ⟨x,u⟩ < 0}"*.

Both hypotheses on `v` are used and neither can be dropped: `⟨v,u⟩ = 0` is what keeps `⟨·,u⟩`
constant along the period, so that the translates stay inside the same stripe, and
`k > |⟨v,ũ⟩|` is what makes consecutive translates overlap in the `ũ` coordinate, so that they
leave no gap.  The witness `j` is the quotient of `⟨w,ũ⟩` by `|⟨v,ũ⟩|`. -/
theorem exists_mem_kmBox_of_stripe {u v : ℤ × ℤ} {k : ℤ} (hu : u ≠ 0) (hv : v ≠ 0)
    (hperp : innerZ v u = 0) (hk : |innerZ v (KM.perpOf u)| < k)
    {w : ℤ × ℤ} (h1 : -k < innerZ w u) (h2 : innerZ w u < 0) :
    ∃ z ∈ kmBox u k, ∃ j : ℤ, w = z + j • v := by
  set β : ℤ := innerZ v (KM.perpOf u) with hβ
  have hβ0 : β ≠ 0 := innerZ_perp_ne_zero hu hv hperp
  set s : ℤ := innerZ w (KM.perpOf u) with hs
  set m : ℤ := |β| with hm
  have hmpos : 0 < m := abs_pos.mpr hβ0
  set q : ℤ := s / m with hq
  have hdvd : m * q + s % m = s := Int.mul_ediv_add_emod s m
  have hr0 : 0 ≤ s % m := Int.emod_nonneg s (ne_of_gt hmpos)
  have hr1 : s % m < m := Int.emod_lt_of_pos s hmpos
  refine ⟨w - (if 0 < β then q else -q) • v, ?_, (if 0 < β then q else -q), by abel⟩
  have hjβ : (if 0 < β then q else -q) * β = m * q := by
    rcases lt_trichotomy β 0 with h | h | h
    · rw [if_neg (not_lt.mpr h.le), hm, abs_of_neg h]; ring
    · exact absurd h hβ0
    · rw [if_pos h, hm, abs_of_pos h]; ring
  have hzu : innerZ (w - (if 0 < β then q else -q) • v) u = innerZ w u := by
    rw [innerZ_sub, innerZ_zsmul, hperp, mul_zero, sub_zero]
  have hzp : innerZ (w - (if 0 < β then q else -q) • v) (KM.perpOf u) = s % m := by
    rw [innerZ_sub, innerZ_zsmul, ← hβ, hjβ, ← hs]
    linarith
  rw [mem_kmBox hu, hzu, hzp]
  refine ⟨h1, h2, by linarith, by linarith⟩

/-! #### The glue -/

/-- **Kari–Moutot Lemma 14** (p. 136, verbatim): *"For any `d, e ∈ X` such that `φd = φe` holds:
`d|_B = e|_B ⟹ d|_H = e|_H`"*, with `B = B_u^k` and `H = H_{−u}`, proved from

* `Nivat.KM14.lemma14_stripe` — the `v`-periodicity of `d − e`, which carries the agreement from
  `B` to the stripe `S`;
* `exists_mem_kmBox_of_stripe` — that `S` is the *full* stripe `{x | −k < ⟨x,u⟩ < 0}`;
* `hwin` — Kari–Moutot's property (2), *"the contents of a configuration in the discrete box
  `B_u^k` are enough to uniquely determine the contents in cell `0`"*, which
  `exists_kmBox_window` below derives from determinism in direction `u`.

The last sentence of the paper's proof, *"Applying (2) on suitable translates of `d` and `e`
allows us to conclude that `d|_H = e|_H`"*, is the induction `main`: the window applied at the
translate `w` reads `d` and `e` only at cells `z + w` with `⟨z,u⟩ ∈ (−k, 0)`, i.e. strictly
lower in `⟨·, u⟩` than `w` itself, so agreement propagates upwards from the stripe, one level of
`⟨·, u⟩` at a time, and covers everything with `⟨w,u⟩ > −k` — in particular all of
`halfPlane (-u) = {w | ⟨w,u⟩ > 0}`.

Hypotheses: `hperp` is *"`u` is perpendicular to some `v_i`; without loss of generality `i = 1`
… we denote `φ = φ₁` and `v = v₁`"* (p. 135), and `hk` is *"we can choose `k` so that
`k > |⟨ũ, v⟩|`"* (p. 136).  Both are properties of Kari–Moutot's own choice of `φ` and `k`, not
extra assumptions. -/
theorem lemma14HalfPlane_of_stripe_and_window {c : Config ℤ} {φ : LaurentTwo ℤ}
    {B : Finset (ℤ × ℤ)} {u v : ℤ × ℤ} {k : ℤ}
    (hu : u ≠ 0) (hv : v ≠ 0) (hperp : innerZ v u = 0) (hphi : φ = mono v - 1)
    (hk : |innerZ v (KM.perpOf u)| < k) (hB : B = kmBox u k)
    (hwin : ∀ p ∈ orbitClosure c, ∀ q ∈ orbitClosure c,
      (∀ z ∈ B, p z = q z) → p 0 = q 0) :
    Lemma14HalfPlane c φ B (-u) := by
  subst hphi
  subst hB
  intro d hd e he hact hBagree
  have hkpos : 0 < k := lt_of_le_of_lt (abs_nonneg _) hk
  -- Step 1+2: agreement on the whole stripe `−k < ⟨·,u⟩ < 0`.
  have hstripe : ∀ w : ℤ × ℤ, -k < innerZ w u → innerZ w u < 0 → d w = e w := by
    intro w h1 h2
    exact KM14.lemma14_stripe hv hact hBagree w
      (exists_mem_kmBox_of_stripe hu hv hperp hk h1 h2)
  -- Step 3: induction upwards in `⟨·,u⟩`, applying the window at each translate.
  have main : ∀ N : ℕ, ∀ w : ℤ × ℤ, -k < innerZ w u → innerZ w u + k ≤ (N : ℤ) → d w = e w := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro w h1 h2
      rcases lt_or_ge (innerZ w u) 0 with hneg | hpos
      · exact hstripe w h1 hneg
      · have hagr : ∀ z ∈ kmBox u k, T w d z = T w e z := by
          intro z hz
          rw [mem_kmBox hu] at hz
          have hsum : innerZ (z + w) u = innerZ z u + innerZ w u := innerZ_add z w u
          show d (z + w) = e (z + w)
          exact ih ((innerZ (z + w) u + k).toNat) (by omega) (z + w) (by omega) (by omega)
        have hzero := hwin (T w d) (T_mem_of_mem_orbitClosure hd w) (T w e)
          (T_mem_of_mem_orbitClosure he w) hagr
        have h0 : d (0 + w) = e (0 + w) := hzero
        rwa [zero_add] at h0
  -- The conclusion half plane is the other side, `⟨z,u⟩ > 0`.
  intro z hz
  rw [mem_halfPlane_iff] at hz
  have hzu : 0 < innerZ z u := by
    simp only [innerZ]
    simp only [Prod.fst_neg, Prod.snd_neg, mul_neg] at hz
    linarith
  exact main ((innerZ z u + k).toNat) z (by omega) (by omega)

/-! #### The determinism window, for a configuration of finite range -/

/-- Every value of a member of the orbit closure is a value of the base configuration.  This is
what replaces the `[Finite α]` of `Nivat.KMBox.exists_window_of_det`: the compactness argument
only ever needs the values that actually occur. -/
theorem mem_range_of_mem_orbitClosure {α : Type*} {c x : Config α} (hx : x ∈ orbitClosure c)
    (z : ℤ × ℤ) : x z ∈ Set.range c :=
  ⟨(hx {z}).choose + z, ((hx {z}).choose_spec z (Finset.mem_singleton_self z)).symm⟩

/-- `Nivat.KMBox.exists_pair_limit` for configurations whose values lie in a fixed finite set of
integers, rather than over a finite alphabet.  Same ultrafilter argument, with
`Ultrafilter.eq_pure_of_finite_mem` in place of `Ultrafilter.eq_pure_of_finite`. -/
theorem exists_pair_limit_of_finite_range {A : Set ℤ} (hA : A.Finite) (x y : ℕ → Config ℤ)
    (hx : ∀ n w, x n w ∈ A) (hy : ∀ n w, y n w ∈ A) :
    ∃ x' y' : Config ℤ, ∀ (W : Finset (ℤ × ℤ)) (M : ℕ), ∃ n : ℕ, M ≤ n ∧
      (∀ w ∈ W, x' w = x n w) ∧ (∀ w ∈ W, y' w = y n w) := by
  classical
  set 𝔲 : Ultrafilter ℕ := Ultrafilter.of Filter.atTop with h𝔲
  have key : ∀ w : ℤ × ℤ, ∃ p : ℤ × ℤ, {n : ℕ | (x n w, y n w) = p} ∈ 𝔲 := by
    intro w
    have huniv : (fun n : ℕ => (x n w, y n w)) ⁻¹' (A ×ˢ A) = Set.univ := by
      ext n
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, iff_true]
      exact ⟨hx n w, hy n w⟩
    have hmemmap : (A ×ˢ A) ∈ Ultrafilter.map (fun n : ℕ => (x n w, y n w)) 𝔲 := by
      rw [Ultrafilter.mem_map, huniv]
      exact Filter.univ_mem
    obtain ⟨p, -, hp⟩ := Ultrafilter.eq_pure_of_finite_mem (hA.prod hA) hmemmap
    refine ⟨p, ?_⟩
    have hsing : ({p} : Set (ℤ × ℤ)) ∈ Ultrafilter.map (fun n : ℕ => (x n w, y n w)) 𝔲 := by
      rw [hp]; exact Ultrafilter.mem_pure.mpr rfl
    rwa [Ultrafilter.mem_map] at hsing
  choose z hz using key
  refine ⟨fun w => (z w).1, fun w => (z w).2, ?_⟩
  intro W M
  have h1 : {n : ℕ | M ≤ n} ∈ 𝔲 := Ultrafilter.of_le Filter.atTop (Filter.mem_atTop M)
  have h2 : (⋂ w ∈ W, {n : ℕ | (x n w, y n w) = z w}) ∈ 𝔲 :=
    (Filter.biInter_finset_mem W).mpr fun w _ => hz w
  obtain ⟨n, hn⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem h1 h2)
  have hn2 := hn.2
  simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hn2
  refine ⟨n, hn.1, fun w hw => ?_, fun w hw => ?_⟩
  · exact (congrArg Prod.fst (hn2 w hw)).symm
  · exact (congrArg Prod.snd (hn2 w hw)).symm

/-- **Kari–Moutot §2.2, the determinism window**, for `Config ℤ` with finite range: the exact
statement of `Nivat.KMBox.exists_window_of_det`, with `[Finite α]` traded for
`(Set.range c).Finite`.  Same proof, on the finite value set `Set.range c`. -/
theorem exists_window_of_det_of_finite_range {c : Config ℤ} (hc : (Set.range c).Finite)
    {μ : ℝ × ℝ}
    (hdet : ∀ p ∈ orbitClosure c, ∀ q ∈ orbitClosure c,
      (∀ z : ℤ × ℤ, inner2 μ z < 0 → p z = q z) → p = q) :
    ∃ B : Finset (ℤ × ℤ), (∀ z ∈ B, inner2 μ z < 0) ∧
      ∀ p ∈ orbitClosure c, ∀ q ∈ orbitClosure c,
        (∀ z ∈ B, p z = q z) → p 0 = q 0 := by
  classical
  by_contra hcon
  push Not at hcon
  set H : ℕ → Finset (ℤ × ℤ) :=
    fun n => (KMBox.boxUpTo n).filter (fun z => inner2 μ z < 0) with hH
  have hHsub : ∀ n, ∀ z ∈ H n, inner2 μ z < 0 := fun n z hz => (Finset.mem_filter.mp hz).2
  have hfail : ∀ n : ℕ, ∃ p ∈ orbitClosure c, ∃ q ∈ orbitClosure c,
      (∀ z ∈ H n, p z = q z) ∧ p 0 ≠ q 0 := by
    intro n
    obtain ⟨p, hp, q, hq, hagr, hne⟩ := hcon (H n) (hHsub n)
    exact ⟨p, hp, q, hq, hagr, hne⟩
  choose p hp q hq hagr hne using hfail
  obtain ⟨p', q', hlim⟩ := exists_pair_limit_of_finite_range hc p q
    (fun n w => mem_range_of_mem_orbitClosure (hp n) w)
    (fun n w => mem_range_of_mem_orbitClosure (hq n) w)
  have hp' : p' ∈ orbitClosure c :=
    KMBox.mem_orbitClosure_of_pointwise_limit hp fun W M => (hlim W M).imp fun _ h => ⟨h.1, h.2.1⟩
  have hq' : q' ∈ orbitClosure c :=
    KMBox.mem_orbitClosure_of_pointwise_limit hq fun W M => (hlim W M).imp fun _ h => ⟨h.1, h.2.2⟩
  have hne' : p' 0 ≠ q' 0 := by
    obtain ⟨n, -, h1, h2⟩ := hlim {0} 0
    rw [h1 0 (Finset.mem_singleton_self _), h2 0 (Finset.mem_singleton_self _)]
    exact hne n
  have hagr' : ∀ z : ℤ × ℤ, inner2 μ z < 0 → p' z = q' z := by
    intro z hz
    obtain ⟨n, hnk, h1, h2⟩ := hlim {z} (Denumerable.eqv (ℤ × ℤ) z + 1)
    have hzH : z ∈ H n := Finset.mem_filter.mpr ⟨KMBox.mem_boxUpTo (by omega), hz⟩
    rw [h1 z (Finset.mem_singleton_self _), h2 z (Finset.mem_singleton_self _)]
    exact hagr n z hzH
  exact hne' (congrFun (hdet p' hp' q' hq' hagr') 0)

/-- **Property (2) of Kari–Moutot §4 for the specific box `B_u^k`**, with `k` as large as
required: *"Let `k` be such that the contents of the discrete box `B = B_u^k` determine the
content of cell `0` … As pointed out in Section 2.2, any sufficiently large `k` can be used."*

The compactness argument delivers *some* finite window inside `H_u`; enlarging `k` past every
coordinate of that window puts it inside `B_u^k`, and a larger window determines at least as
much.  The free parameter `k₀` is what lets the caller also demand `k > |⟨v,ũ⟩|` and
`k > ⟨u,u⟩`. -/
theorem exists_kmBox_window {c : Config ℤ} {u : ℤ × ℤ} (hc : (Set.range c).Finite) (hu : u ≠ 0)
    (hdet : toReal u ∉ ONED c) (k₀ : ℤ) :
    ∃ k : ℤ, k₀ < k ∧ ∀ p ∈ orbitClosure c, ∀ q ∈ orbitClosure c,
      (∀ z ∈ kmBox u k, p z = q z) → p 0 = q 0 := by
  classical
  obtain ⟨B₀, hB₀side, hB₀win⟩ := exists_window_of_det_of_finite_range hc
    ((KM.notMem_ONED_iff_det (KM.toReal_ne_zero hu)).mp hdet)
  set S : ℤ := ∑ z ∈ B₀, (|innerZ z u| + |innerZ z (KM.perpOf u)|) with hSdef
  refine ⟨max (k₀ + 1) (S + 1), lt_of_lt_of_le (lt_add_one k₀) (le_max_left _ _), ?_⟩
  intro P hP Q hQ hagree
  refine hB₀win P hP Q hQ ?_
  intro z hz
  refine hagree z ?_
  have hsum : |innerZ z u| + |innerZ z (KM.perpOf u)| ≤ S :=
    Finset.single_le_sum (f := fun z => |innerZ z u| + |innerZ z (KM.perpOf u)|)
      (fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hz
  have hSk : S + 1 ≤ max (k₀ + 1) (S + 1) := le_max_right _ _
  have hneg : innerZ z u < 0 := (mem_halfPlane_iff_inner2 u z).mpr (hB₀side z hz)
  obtain ⟨ha1, ha2⟩ := abs_le.mp (show |innerZ z u| ≤ S by
    linarith [abs_nonneg (innerZ z (KM.perpOf u))])
  obtain ⟨hb1, hb2⟩ := abs_le.mp (show |innerZ z (KM.perpOf u)| ≤ S by
    linarith [abs_nonneg (innerZ z u)])
  rw [mem_kmBox hu]
  exact ⟨by linarith, hneg, by linarith, by linarith⟩

/-- **`Lemma14HalfPlane` is a theorem**, for Kari–Moutot's own box and their own `φ`.

This is the end of the debt recorded in the note on `Lemma14HalfPlane`: given the data of §4 —
finite alphabet (`hc`), a direction `u` of determinism of `O(c)‾` (`hdet`), and the factor
`φ = x^v − 1` of the annihilator whose `v` is perpendicular to `u` (`hperp`, `hphi`) — the box
`B = B_u^k` of §2.2 exists, is nonempty, sits inside `H_u`, and satisfies Lemma 14 for the
opposite half plane `H_{−u}`.

The perpendicularity `hperp` is not an extra assumption but the standing situation of §4:
Kari–Moutot obtain it from Proposition 13 (*"By the proposition above, `u` is perpendicular to
some `v_i`.  Without loss of generality, we may assume `i = 1`"*, p. 135) as soon as `u` is a
*one-sided* direction of determinism, which is the case Proposition 18 is about. -/
theorem exists_lemma14HalfPlane_of_det {c : Config ℤ} {φ : LaurentTwo ℤ} {u v : ℤ × ℤ}
    (hc : (Set.range c).Finite) (hu : u ≠ 0) (hv : v ≠ 0)
    (hperp : innerZ v u = 0) (hphi : φ = mono v - 1) (hdet : toReal u ∉ ONED c) :
    ∃ B : Finset (ℤ × ℤ), B.Nonempty ∧ (∀ z ∈ B, z ∈ halfPlane u) ∧
      Lemma14HalfPlane c φ B (-u) := by
  obtain ⟨k, hk, hwin⟩ :=
    exists_kmBox_window hc hu hdet (max (innerZ u u) |innerZ v (KM.perpOf u)|)
  have hk1 : innerZ u u < k := lt_of_le_of_lt (le_max_left _ _) hk
  have hk2 : |innerZ v (KM.perpOf u)| < k := lt_of_le_of_lt (le_max_right _ _) hk
  exact ⟨kmBox u k, ⟨-u, neg_mem_kmBox hu hk1⟩, kmBox_subset_halfPlane hu k,
    lemma14HalfPlane_of_stripe_and_window hu hv hperp hphi hk2 rfl hwin⟩

/-- **The hypotheses of `exists_lemma14HalfPlane_of_det` are jointly satisfiable**, so the
theorem above is not vacuous.

Witness: `c = Nivat.KM.vline`, `u = (0,1)` — a direction of determinism of `O(vline)‾`
(`Nivat.KM.vline_not_ONED_vertical_pos`), since `vline` is constant along columns — and
`v = (1,0)`, which is perpendicular to `u` and is the direction of a genuine factor
`φ = x − 1` of an annihilator of `vline`.  Finiteness of the range is
`Nivat.KM.vline_range_finite`.

Together with `not_lemma14HalfPlane_vline` (the predicate is refutable) this pins the content of
`Lemma14HalfPlane` from both sides: it is neither always true nor unreachable. -/
theorem exists_lemma14HalfPlane_vline :
    ∃ B : Finset (ℤ × ℤ), B.Nonempty ∧ (∀ z ∈ B, z ∈ halfPlane ((0 : ℤ), (1 : ℤ))) ∧
      Lemma14HalfPlane KM.vline (mono ((1 : ℤ), (0 : ℤ)) - 1) B (-((0 : ℤ), (1 : ℤ))) :=
  exists_lemma14HalfPlane_of_det KM.vline_range_finite
    (by intro h; exact absurd (congrArg Prod.snd h) (by norm_num))
    (by intro h; exact absurd (congrArg Prod.fst h) (by norm_num))
    (by norm_num [innerZ]) rfl KM.vline_not_ONED_vertical_pos

/-! ### Part (a) -/

/-- **Kari–Moutot Lemma 16(a)** (p. 137): *"`φd₁ = ⋯ = φdₙ`"*.

Verbatim proof: *"Because `φc_{i₁} = φc_{i₂}` we have, for any `n ∈ ℕ`,
`φτ^{nu}(c_{i₁}) = τ^{nu}(φc_{i₁}) = τ^{nu}(φc_{i₂}) = φτ^{nu}(c_{i₂})`.  Function `c ↦ φc` is
continuous in the topology so `φd_{i₁} = ⋯ = φd_{i₂}`."*

Formally, "continuity of `c ↦ φc`" is the finiteness of `φ.coeff.support`: the value of
`act φ x` at `z` reads `x` only on the finite window `z + φ.coeff.support`, so a single time `m`
from the joint limit at that window transports the identity.  `Nivat.act_T` is the first
displayed chain of equalities.

Note that the hypothesis is `hc_ann_eq`, *not* `act φ (c_seq i) = 0`: in §4 the annihilator of
`c` is the product `φ₁ ⋯ φ_m` and `φ = φ₁` is one factor of it, so `φ` does not annihilate the
`cᵢ` and this part is not trivial. -/
theorem act_eq_of_jointSubseqLimit {φ : LaurentTwo ℤ} {u : ℤ × ℤ} {n : ℕ}
    {c_seq d_seq : Fin n → Config ℤ}
    (hc_ann_eq : ∀ i j, act φ (c_seq i) = act φ (c_seq j))
    (hjoint : JointSubseqLimit c_seq d_seq u) (i j : Fin n) :
    act φ (d_seq i) = act φ (d_seq j) := by
  classical
  funext z
  obtain ⟨m, -, hm⟩ := hjoint (φ.coeff.support.image fun q => z + q) 0
  have key : ∀ k : Fin n, act φ (d_seq k) z = act φ (c_seq k) (z + (m : ℤ) • u) := by
    intro k
    simp only [act_apply]
    refine Finsupp.sum_congr fun q hq => ?_
    have hmem : z + q ∈ φ.coeff.support.image fun q => z + q :=
      Finset.mem_image.mpr ⟨q, hq, rfl⟩
    rw [hm k _ hmem]
    congr 2
    abel
  rw [key i, key j, congrFun (hc_ann_eq i j) _]

/-! ### Part (b) -/

/-- **The engine of Kari–Moutot Lemma 16(b)** (p. 137): if two members of a *joint* family of
subsequential limits agree on one translate `B + t` of the box, then the two source
configurations are **equal**.

This is the displayed argument of the paper, contraposed: agreement of `d_{i}` and `d_{j}` on
`B + t` is pushed back to agreement of `T^{t + m•u} (c_i)` and `T^{t + m•u} (c_j)` on `B` at a
single joint time `m`, Lemma 14 upgrades that to agreement on `halfPlane u`, i.e. `c_i = c_j` on
`halfPlane u + t + m•u`, and letting `m → ∞` those half planes exhaust `ℤ²`.

The exhaustion is the only arithmetic: for a fixed cell `w`, `w − t − m • u ∈ halfPlane u`
as soon as `m` exceeds `|⟨w, u⟩ − ⟨t, u⟩|`, because `⟨u, u⟩ ≥ 1` (`inner_self_pos`).  Crucially
the *same* `m` must serve every index, which is what `JointSubseqLimit` supplies and what
`∀ i, d_seq i ∈ subseqLimits (c_seq i) u` does not. -/
theorem eq_of_agree_on_translated_box {φ : LaurentTwo ℤ} {c : Config ℤ} {u : ℤ × ℤ}
    {B : Finset (ℤ × ℤ)} (hu : u ≠ 0) (h14 : Lemma14HalfPlane c φ B u)
    {n : ℕ} {c_seq d_seq : Fin n → Config ℤ}
    (hc_orbit : ∀ i, c_seq i ∈ orbitClosure c)
    (hc_ann_eq : ∀ i j, act φ (c_seq i) = act φ (c_seq j))
    (hjoint : JointSubseqLimit c_seq d_seq u) (i j : Fin n) (t : ℤ × ℤ)
    (hagree : ∀ z ∈ B.image (· + t), d_seq i z = d_seq j z) :
    c_seq i = c_seq j := by
  classical
  have hS : 0 < u.1 * u.1 + u.2 * u.2 := inner_self_pos hu
  funext w
  -- The time bound that puts `w` inside the translated half plane.
  set D : ℤ := (w.1 * u.1 + w.2 * u.2) - (t.1 * u.1 + t.2 * u.2) with hD
  obtain ⟨m, hmN, hm⟩ := hjoint (B.image (· + t)) (D.natAbs + 1)
  -- `m ≥ |D| + 1` and `⟨u,u⟩ ≥ 1`, so `D - m * ⟨u,u⟩ < 0`.
  have hmbig : D - (m : ℤ) * (u.1 * u.1 + u.2 * u.2) < 0 := by
    have h1 : (m : ℤ) ≤ (m : ℤ) * (u.1 * u.1 + u.2 * u.2) :=
      le_mul_of_one_le_right (by positivity) hS
    have h2 : (D.natAbs + 1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hmN
    have h3 : D ≤ (D.natAbs : ℤ) := Int.le_natAbs
    omega
  -- The translate at which Lemma 14 is applied.
  set v : ℤ × ℤ := t + (m : ℤ) • u with hv
  have hdo : T v (c_seq i) ∈ orbitClosure c := T_mem_of_mem_orbitClosure (hc_orbit i) v
  have heo : T v (c_seq j) ∈ orbitClosure c := T_mem_of_mem_orbitClosure (hc_orbit j) v
  -- Same product with `φ`, because translation commutes with `act`.
  have hann : act φ (T v (c_seq i)) = act φ (T v (c_seq j)) := by
    rw [act_T, act_T, hc_ann_eq i j]
  -- They agree on `B`: this is `hagree`, read at the joint time `m`.
  have hBagree : ∀ z ∈ B, T v (c_seq i) z = T v (c_seq j) z := by
    intro b hb
    have hmem : b + t ∈ B.image (· + t) := Finset.mem_image.mpr ⟨b, hb, rfl⟩
    have hshift : b + v = (b + t) + (m : ℤ) • u := by rw [hv]; abel
    show c_seq i (b + v) = c_seq j (b + v)
    rw [hshift, ← hm i _ hmem, ← hm j _ hmem]
    exact hagree _ hmem
  -- Lemma 14 upgrades that to the whole half plane.
  have hhalf := h14 _ hdo _ heo hann hBagree
  -- Apply it at `w - v`, which lies in the half plane by the choice of `m`.
  have hwv : w - v ∈ halfPlane u := by
    rw [mem_halfPlane_iff, hv]
    show (w - (t + (m : ℤ) • u)).1 * u.1 + (w - (t + (m : ℤ) • u)).2 * u.2 < 0
    have hsmul1 : ((m : ℤ) • u).1 = (m : ℤ) * u.1 := by
      simp only [Prod.smul_fst, smul_eq_mul]
    have hsmul2 : ((m : ℤ) • u).2 = (m : ℤ) * u.2 := by
      simp only [Prod.smul_snd, smul_eq_mul]
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, hsmul1, hsmul2]
    have hexp : (w.1 - (t.1 + (m : ℤ) * u.1)) * u.1 + (w.2 - (t.2 + (m : ℤ) * u.2)) * u.2
        = D - (m : ℤ) * (u.1 * u.1 + u.2 * u.2) := by rw [hD]; ring
    rw [hexp]
    exact hmbig
  have := hhalf _ hwv
  show c_seq i w = c_seq j w
  have hcancel : w - v + v = w := by abel
  rw [show T v (c_seq i) (w - v) = c_seq i w by show c_seq i (w - v + v) = _; rw [hcancel],
    show T v (c_seq j) (w - v) = c_seq j w by show c_seq j (w - v + v) = _; rw [hcancel]] at this
  exact this

/-- **Kari–Moutot Lemma 16(b)** (p. 137), verbatim: *"Configurations `dᵢ` are pairwise different
on translated discrete boxes `B′ = B − t` for all `t ∈ ℤ²`."*

The contrapositive of `eq_of_agree_on_translated_box`: the contradiction the paper derives is
with `c_{i₁} ≠ c_{i₂}` (the pairwise distinctness of the *sources*), so this needs no hypothesis
about the `dᵢ` at all.

Replaces the declaration of the same name that this file used to carry, which was an `axiom`,
then a `sorry`, and false in both versions — see "History" in the module docstring for the two
counterexamples.  In particular `B.Nonempty` and `d₁ ≠ d₂` are *not* hypotheses here: the
former is unnecessary because `Lemma14HalfPlane c φ ∅ u` is already strong enough to contradict
`c_seq i ≠ c_seq j` (so the statement holds ex falso at `B = ∅`, honestly rather than by
weakening), and the latter is derived below. -/
theorem distinct_configs_differ_on_translates {φ : LaurentTwo ℤ} {c : Config ℤ} {u : ℤ × ℤ}
    {B : Finset (ℤ × ℤ)} (hu : u ≠ 0) (h14 : Lemma14HalfPlane c φ B u)
    {n : ℕ} {c_seq d_seq : Fin n → Config ℤ}
    (hc_orbit : ∀ i, c_seq i ∈ orbitClosure c)
    (hc_distinct : ∀ i j, i ≠ j → c_seq i ≠ c_seq j)
    (hc_ann_eq : ∀ i j, act φ (c_seq i) = act φ (c_seq j))
    (hjoint : JointSubseqLimit c_seq d_seq u) (i j : Fin n) (hij : i ≠ j) (t : ℤ × ℤ) :
    ∃ z ∈ B.image (· + t), d_seq i z ≠ d_seq j z := by
  by_contra hcon
  push Not at hcon
  exact hc_distinct i j hij
    (eq_of_agree_on_translated_box hu h14 hc_orbit hc_ann_eq hjoint i j t hcon)

/-- **`hd_distinct` is a theorem, not a hypothesis.**  Pairwise distinctness of the limits
`d_seq` follows from pairwise distinctness of the sources `c_seq`.

This is what the previous version of `lemma16` was forced to assume, and its derivation was the
outstanding debt of this file.  It is a corollary of Lemma 16(b): distinctness *on a box* is
stronger than distinctness.

`B.Nonempty` is **not** needed, contrary to what one might expect from reading
`distinct_configs_differ_on_translates` alone.  At `B = ∅` the hypothesis
`Lemma14HalfPlane c φ ∅ u` says that *any* two elements of `orbitClosure c` with the same
`φ`-product agree on `halfPlane u`; together with `hc_distinct` and `hc_ann_eq` that is already
contradictory once `n ≥ 2`, so the conclusion holds ex falso rather than by weakening.  For the
`B = B_u^k` of Kari–Moutot §2.2 the box is nonempty anyway (it contains `−u` once
`k > ⟨u, u⟩`), so the question never arises at the intended call site. -/
theorem distinct_of_jointSubseqLimit {φ : LaurentTwo ℤ} {c : Config ℤ} {u : ℤ × ℤ}
    {B : Finset (ℤ × ℤ)} (hu : u ≠ 0) (h14 : Lemma14HalfPlane c φ B u)
    {n : ℕ} {c_seq d_seq : Fin n → Config ℤ}
    (hc_orbit : ∀ i, c_seq i ∈ orbitClosure c)
    (hc_distinct : ∀ i j, i ≠ j → c_seq i ≠ c_seq j)
    (hc_ann_eq : ∀ i j, act φ (c_seq i) = act φ (c_seq j))
    (hjoint : JointSubseqLimit c_seq d_seq u) :
    ∀ i j, i ≠ j → d_seq i ≠ d_seq j := by
  intro i j hij heq
  obtain ⟨z, -, hz⟩ :=
    distinct_configs_differ_on_translates hu h14 hc_orbit hc_distinct hc_ann_eq hjoint i j hij 0
  exact hz (congrFun heq z)

/-! ### Lemma 16 -/

/-- **Kari–Moutot Lemma 16** (journal version, §4, p. 137), verbatim:

> "Let `d₁, …, dₙ` be defined as above.  Then (a) `φd₁ = ⋯ = φdₙ`, and (b) Configurations `dᵢ`
> are pairwise different on translated discrete boxes `B′ = B − t` for all `t ∈ ℤ²`."

**Both parts are proved.**  No `sorry`, no new `axiom`.

### Statement change relative to the previous version of this file

Hypotheses **removed**:

* `hd_distinct : ∀ i j, i ≠ j → d_seq i ≠ d_seq j` — this was the debt.  It is now the derived
  `distinct_of_jointSubseqLimit`.  Kari–Moutot never assume it; their part (b) contradicts
  `c_{i₁} ≠ c_{i₂}`, which is already in the data as `hc_distinct`.
* `B.Nonempty` — not used by either part.
* `act φ (c_seq i) = 0` — *not in the paper*: in §4, `φ = φ₁` is one factor of the annihilator
  `φ₁ ⋯ φ_m` of `c` and does **not** annihilate the `cᵢ`.  Assuming it trivialised part (a)
  into `0 = 0`.  Only `hc_ann_eq` (which *is* the paper's *"`φc₁ = ⋯ = φcₙ`"*) is used.
* `(Set.range c).Finite` and `φ ≠ 0` — both were unused.  Finiteness of the alphabet is what a
  caller needs to *build* `hjoint` via `exists_jointSubseqLimit`, so it moves to the call site
  rather than disappearing.

Hypotheses **added**:

* `h14 : Lemma14HalfPlane c φ B u` — **Kari–Moutot Lemma 14, p. 136**, verbatim *"For any
  `d, e ∈ X` such that `φd = φe` holds: `d|_B = e|_B ⟹ d|_H = e|_H`"*.  This is the only thing
  in §4 that ties the box `B` to the direction `u`, and without it part (b) is false for every
  choice of extra hypotheses about the `dᵢ` (module docstring, "History").  In Kari–Moutot's
  own development it is discharged from their property (2) of §2.2 plus the `v`-periodicity of
  `d − e`; here it is discharged the same way, by `exists_lemma14HalfPlane_of_det`, so a caller
  who has the data of §4 (finite range, determinism in direction `u`, and the perpendicular
  factor `φ = x^v − 1` of the annihilator) can supply `h14` for the specific `B = B_u^k` of §2.2
  — at the direction `-u`, which is the side Kari–Moutot's `H = H_{−u}` lives on.

Hypothesis **strengthened in form** (same mathematical content as the paper, strictly stronger
than what was there before):

* `hjoint : JointSubseqLimit c_seq d_seq u` replaces
  `hd_limit : ∀ i, d_seq i ∈ subseqLimits (c_seq i) u`.  The paper takes all `n` limits along
  **one** sequence of times (*"there exists `n₁ < n₂ < n₃ …` such that `dᵢ = lim_j τ^{nⱼ u}(cᵢ)`
  exists for all `i`"*, p. 137); the old hypothesis let each `i` pick its own times, which is
  what made the old statement false.  `JointSubseqLimit.mem_subseqLimits` recovers the old form,
  and `exists_jointSubseqLimit` shows the new one is satisfiable — by exactly the compactness
  the paper cites — so this is a faithfulness fix, not a convenience.

Nothing here depends on the maximality of `n` from Corollary 15.  That is consumed by
Lemma 17, not by Lemma 16. -/
theorem lemma16 {φ : LaurentTwo ℤ} {c : Config ℤ} {u : ℤ × ℤ} {B : Finset (ℤ × ℤ)}
    (hu : u ≠ 0) (h14 : Lemma14HalfPlane c φ B u)
    {n : ℕ} {c_seq d_seq : Fin n → Config ℤ}
    (hc_orbit : ∀ i, c_seq i ∈ orbitClosure c)
    (hc_distinct : ∀ i j, i ≠ j → c_seq i ≠ c_seq j)
    (hc_ann_eq : ∀ i j, act φ (c_seq i) = act φ (c_seq j))
    (hjoint : JointSubseqLimit c_seq d_seq u) :
    (∀ i j, act φ (d_seq i) = act φ (d_seq j)) ∧
    (∀ i j (t : ℤ × ℤ), i ≠ j →
      ∃ z : ℤ × ℤ, z ∈ B.image (· + t) ∧ d_seq i z ≠ d_seq j z) := by
  refine ⟨fun i j => act_eq_of_jointSubseqLimit hc_ann_eq hjoint i j, fun i j t hij => ?_⟩
  obtain ⟨z, hz, hne⟩ :=
    distinct_configs_differ_on_translates hu h14 hc_orbit hc_distinct hc_ann_eq hjoint i j hij t
  exact ⟨z, hz, hne⟩

end Nivat.KM16
