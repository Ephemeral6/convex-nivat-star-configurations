/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Theorem114Step3
import Nivat.External.KSCorollary
import Nivat.External.KSDecomposition

/-!
# Colle Theorem 1.14, step 3 — proved

`Nivat/External/Colle/Theorem114.lean` reduces Colle's Theorem 1.14 to two statements:

* `Nivat.Colle.exists_doublyPeriodic_in_orbitClosure` (step 2; closed 2026-09-14, measured
  `[propext, Classical.choice, Quot.sound]`), and
* `Nivat.Colle.doublyPeriodic_of_orbitClosure_witness` (step 3), which used to be a `sorry`.

This file **proves step 3**.  It lives downstream of `Theorem114Step3.lean` because it uses
`Nivat.Colle3.doublyPeriodic_of_isPeriodic` (Colle's Proposition 1.8 plus Boyle–Lind), which is
proved there; the two statements were therefore moved out of `Theorem114.lean` into this file,
character for character.

## The proof

Colle's own §3.1 gets from `x_per` to `η` through Lemma 3.5 (a maximal-set construction giving
an `(ℓ, ℓ')`-region), Claim 3.6 and Claim 3.7.  The argument below replaces that whole block by
a *nearest-defect* limit, which is shorter and needs no region combinatorics at all.

Assume `ξ` is not doubly periodic while `x ∈ X_ξ` is.

1. **Nearest defect.**  For each `m`, translate `ξ` so that it agrees with `x` on the square
   `[-m,m]²`; call the translate `ϑ_m`.  The agreement set `A_m` is a proper subset of `ℤ²`
   (otherwise `ξ` would be a translate of `x`, hence doubly periodic), so it has a point
   `z_m ∉ A_m` of least Euclidean norm, and `‖z_m‖ > m`.  Re-centre at `z_m`:
   `χ_m := T^{z_m} ϑ_m` and `p_m := T^{z_m} x` disagree at the origin, and agree on the
   *Euclidean ball* `{z : ‖z + z_m‖ < ‖z_m‖}`, i.e. on `{z : ‖z‖² < 2⟨z, -z_m⟩}`.

2. **Limit.**  Along a fixed ultrafilter `U ≤ atTop` take the pointwise limits `χ` of `χ_m` and
   `p` of `p_m`, and the limit `e` of the unit vectors `e_m := -z_m/‖z_m‖₁`.  Balls of radius
   `r_m → ∞` through the origin with centre direction `e_m → e` converge to the half-plane
   `{⟨z, e⟩ > 0}`; so `χ = p` on `{z : 1 ≤ ⟨z, e⟩}` while `χ 0 ≠ p 0`.  Both `χ` and `p` lie in
   `X_ξ`, and `p` inherits every period of `x`, so `p` is doubly periodic.

3. **The limit direction is rational (Colle Lemma 2.6).**  `χ - p` is annihilated by
   `∏ᵢ (X^{hᵢ} - 1)` (Kari–Szabados Corollary 1 applied to `ξ`, transported to the orbit
   closure) and vanishes on a half-plane without vanishing identically; by the Kari–Szabados
   decomposition and `Nivat.Colle.sum_eq_zero_of_halfPlane` this forces `⟨hᵢ, e⟩ = 0` for some
   `i`.  So some nonzero lattice vector is tangent to the limit half-plane.

4. **Proposition 2.12.**  A suitable multiple `u` of that `hᵢ` is a period of `p`, hence `χ` is
   `u`-periodic on the half-plane, with `u` tangent to it; `exists_period_multiple_of_halfPlane`
   upgrades this to a global period of `χ`.  So `χ` is periodic, and
   `Nivat.Colle3.doublyPeriodic_of_isPeriodic` — this is where `hONED` is used, and it is the
   only place — makes it *doubly* periodic.

5. **Contradiction.**  `χ` and `p` are both doubly periodic, so they have a common period `q`
   pointing strictly into the half-plane on which they agree; iterating `q` propagates the
   agreement to all of `ℤ²`, contradicting `χ 0 ≠ p 0`.

Step 4 is the only user of `hONED`, which is exactly right: without it the statement is false
(`Nivat.KM.orbitClosure_doublyPeriodic_not_sufficient`), and the counterexample `KM.vline` is
stopped precisely at step 4 — every other step goes through for it.
-/

namespace Nivat.Colle

open Filter Topology

variable {α : Type*}

/-! ### Elementary integer geometry -/

/-- Squared Euclidean norm of a lattice vector. -/
private def nsqZ (z : ℤ × ℤ) : ℤ := z.1 * z.1 + z.2 * z.2

/-- Euclidean inner product of two lattice vectors. -/
private def dotZ (z z' : ℤ × ℤ) : ℤ := z.1 * z'.1 + z.2 * z'.2

private theorem nsqZ_nonneg (z : ℤ × ℤ) : 0 ≤ nsqZ z :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

private theorem nsqZ_add (z z' : ℤ × ℤ) :
    nsqZ (z + z') = nsqZ z + 2 * dotZ z z' + nsqZ z' := by
  simp only [nsqZ, dotZ, Prod.fst_add, Prod.snd_add]; ring

/-- A nonempty set of lattice points has an element of least Euclidean norm. -/
private theorem exists_min_nsqZ {P : ℤ × ℤ → Prop} (hP : ∃ z, P z) :
    ∃ z, P z ∧ ∀ z', P z' → nsqZ z ≤ nsqZ z' := by
  classical
  obtain ⟨z0, hz0⟩ := hP
  have hSne : {k : ℕ | ∃ z, P z ∧ (nsqZ z).toNat = k}.Nonempty := ⟨_, z0, hz0, rfl⟩
  obtain ⟨z, hz, hzk⟩ := Nat.sInf_mem hSne
  refine ⟨z, hz, fun z' hz' => ?_⟩
  have h1 : sInf {k : ℕ | ∃ z, P z ∧ (nsqZ z).toNat = k} ≤ (nsqZ z').toNat :=
    Nat.sInf_le ⟨z', hz', rfl⟩
  have h2 : (nsqZ z).toNat ≤ (nsqZ z').toNat := hzk ▸ h1
  have h3 := nsqZ_nonneg z
  have h4 := nsqZ_nonneg z'
  omega

/-! ### Pointwise limits along an ultrafilter -/

/-- Pointwise limit of a sequence of configurations with values in a fixed finite set,
taken along an ultrafilter.  The conclusion is that on every finite window the limit agrees
with `F m` for an `U`-large set of `m`. -/
private theorem exists_ulimit {S : Set ℤ} (hS : S.Finite) (U : Ultrafilter ℕ)
    (F : ℕ → Config ℤ) (hF : ∀ m z, F m z ∈ S) :
    ∃ y : Config ℤ, ∀ W : Finset (ℤ × ℤ), {m | ∀ z ∈ W, y z = F m z} ∈ U := by
  classical
  have hpt : ∀ z : ℤ × ℤ, ∃ v : ℤ, {m | F m z = v} ∈ U := by
    intro z
    have hsub : (Set.univ : Set ℕ) ⊆ ⋃ v ∈ S, {m | F m z = v} := by
      intro m _
      exact Set.mem_biUnion (hF m z) rfl
    have hmem : (⋃ v ∈ S, {m | F m z = v}) ∈ U :=
      Ultrafilter.mem_coe.mp (Filter.mem_of_superset Filter.univ_mem hsub)
    obtain ⟨v, -, hv⟩ := (Ultrafilter.finite_biUnion_mem_iff (f := U) hS).mp hmem
    exact ⟨v, hv⟩
  choose y hy using hpt
  refine ⟨y, fun W => ?_⟩
  have hmem : (⋂ z ∈ W, {m | F m z = y z}) ∈ (U : Filter ℕ) :=
    (Filter.biInter_finset_mem W).mpr fun z _ => Ultrafilter.mem_coe.mpr (hy z)
  have hsub : (⋂ z ∈ W, {m | F m z = y z}) ⊆ {m | ∀ z ∈ W, y z = F m z} := by
    intro m hm z hz
    exact ((Set.mem_iInter₂.mp hm) z hz).symm
  exact Ultrafilter.mem_coe.mp (Filter.mem_of_superset hmem hsub)

/-! ### Colle Lemma 2.6, in the form used below -/

/-- **Colle Lemma 2.6.**  Two configurations annihilated by `∏ᵢ (X^{hᵢ} - 1)` that agree on a
half-plane whose normal is *transverse to every `hᵢ`* are equal.

This is the exact form in which Colle uses Lemma 2.6 in the proof of Proposition 2.12 (*"as
`(X^{h_1}-1)…(X^{h_m}-1) ∈ ann(η)`, from Lemma 2.6 we get that `ℓ` contains some vector
`h_j`"*).  Contrapositively: a one-sided nonexpansive direction is orthogonal to one of the
`hᵢ`, in particular it is rational. -/
theorem eq_of_agree_halfPlane_of_transverse {n : ℕ} {h : Fin n → ℤ × ℤ}
    (hne : ∀ i, h i ≠ 0) (hnp : Pairwise fun i j => det (h i) (h j) ≠ 0)
    {y y' : Config ℤ}
    (hy : act (∏ i, (mono (h i) - 1) : LaurentTwo ℤ) y = 0)
    (hy' : act (∏ i, (mono (h i) - 1) : LaurentTwo ℤ) y' = 0)
    {w : ℝ × ℝ} {c : ℝ} (hw : ∀ i, inner2 w (h i) ≠ 0)
    (hagree : ∀ z, c ≤ inner2 w z → y z = y' z) : y = y' := by
  classical
  have hd : act (∏ i, (mono (h i) - 1) : LaurentTwo ℤ) (y - y') = 0 := by
    rw [act_sub_right, hy, hy', sub_zero]
  obtain ⟨f, hfp, hfsum⟩ := kari_szabados_decomp' hne hnp hd
  have hfsub : ∀ z, y z - y' z = ∑ i, f i z := hfsum
  have hzero : ∀ z, c ≤ inner2 w z → ∑ i, f i z = 0 := by
    intro z hz
    rw [← hfsub z, hagree z hz, sub_self]
  have hall := sum_eq_zero_of_halfPlane (A := ℤ) Finset.univ f h (w := w) (c := c)
    (fun i _ => hfp i) (fun i _ => hw i) hzero
  funext z
  have h1 := hall z
  have h2 := hfsub z
  linarith [h1, h2]

/-! ### The nearest-defect construction -/

/-- **The construction replacing Colle's Lemma 3.5 / Claim 3.6.**

If `ξ` is not doubly periodic but some `x ∈ X_ξ` is, then `X_ξ` contains a configuration `χ`
and a doubly periodic configuration `p` that agree on a half-plane but differ at the origin. -/
theorem exists_halfPlane_disagreement {ξ : Config ℤ} (hA : (Set.range ξ).Finite)
    {x : Config ℤ} (hx : x ∈ orbitClosure ξ) (hxdp : DoublyPeriodic x)
    (hnd : ¬ DoublyPeriodic ξ) :
    ∃ (χ p : Config ℤ) (w : ℝ × ℝ) (c : ℝ),
      χ ∈ orbitClosure ξ ∧ p ∈ orbitClosure ξ ∧ DoublyPeriodic p ∧ w ≠ 0 ∧
      χ 0 ≠ p 0 ∧ ∀ z, c ≤ inner2 w z → χ z = p z := by
  classical
  -- No translate of `ξ` equals `x`, else `ξ` would inherit the periods of `x`.
  have hTne : ∀ u : ℤ × ℤ, T u ξ ≠ x := by
    intro u hEq
    have hxi : ∀ z, ξ (z + u) = x z := fun z => congrFun hEq z
    have hxi' : ∀ z, x (z - u) = ξ z := by
      intro z
      rw [← hxi (z - u)]
      congr 1
      abel
    have hmem : ∀ a, a ∈ Per x → a ∈ Per ξ := by
      intro a ha
      rw [mem_Per_iff]
      funext z
      show ξ (z + a) = ξ z
      rw [← hxi' (z + a), ← hxi' z, show z + a - u = (z - u) + a by abel, Per.apply ha]
    obtain ⟨a, ha, b, hb, hdet⟩ := hxdp
    exact hnd ⟨a, hmem a ha, b, hmem b hb, hdet⟩
  -- For each `m`: a translate agreeing with `x` on `[-m,m]²`, and a nearest disagreement point.
  have hpick : ∀ m : ℕ, ∃ u zd : ℤ × ℤ,
      (∀ z : ℤ × ℤ, (-(m : ℤ) ≤ z.1 ∧ z.1 ≤ (m : ℤ) ∧ -(m : ℤ) ≤ z.2 ∧ z.2 ≤ (m : ℤ)) →
        ξ (z + u) = x z) ∧
      ξ (zd + u) ≠ x zd ∧ ∀ z, nsqZ z < nsqZ zd → ξ (z + u) = x z := by
    intro m
    obtain ⟨u, hu⟩ := hx ((Finset.Icc (-(m : ℤ)) (m : ℤ)) ×ˢ (Finset.Icc (-(m : ℤ)) (m : ℤ)))
    have hagree : ∀ z : ℤ × ℤ,
        (-(m : ℤ) ≤ z.1 ∧ z.1 ≤ (m : ℤ) ∧ -(m : ℤ) ≤ z.2 ∧ z.2 ≤ (m : ℤ)) → ξ (z + u) = x z := by
      intro z hz
      have hzmem : z ∈ (Finset.Icc (-(m : ℤ)) (m : ℤ)) ×ˢ (Finset.Icc (-(m : ℤ)) (m : ℤ)) := by
        simp only [Finset.mem_product, Finset.mem_Icc]
        exact ⟨⟨hz.1, hz.2.1⟩, ⟨hz.2.2.1, hz.2.2.2⟩⟩
      have hcomm : ξ (z + u) = ξ (u + z) := by rw [add_comm]
      rw [hcomm, ← hu z hzmem]
    have hexists : ∃ z : ℤ × ℤ, ξ (z + u) ≠ x z := by
      by_contra hc
      push_neg at hc
      exact hTne u (funext fun z => hc z)
    obtain ⟨zd, hzd, hmin⟩ := exists_min_nsqZ hexists
    refine ⟨u, zd, hagree, hzd, fun z hz => ?_⟩
    by_contra hcz
    exact absurd (hmin z hcz) (not_le.mpr hz)
  choose uu zz hQ hdef hmin using hpick
  -- Notation for the recentred configurations.
  set chi : ℕ → Config ℤ := fun m z => ξ (z + zz m + uu m) with hchi
  set pp : ℕ → Config ℤ := fun m z => x (z + zz m) with hpp
  have hchiOC : ∀ m, chi m ∈ orbitClosure ξ := by
    intro m
    have := T_mem_of_mem_orbitClosure (T_mem_orbitClosure ξ (uu m)) (zz m)
    convert this using 1
    funext z
    show ξ (z + zz m + uu m) = ξ (z + zz m + uu m)
    rfl
  have hppOC : ∀ m, pp m ∈ orbitClosure ξ := by
    intro m
    have h := T_mem_of_mem_orbitClosure hx (zz m)
    have heq : pp m = T (zz m) x := by funext z; rfl
    rw [heq]; exact h
  -- The agreement ball.
  have hball : ∀ (m : ℕ) (z : ℤ × ℤ), nsqZ z < -2 * dotZ z (zz m) → chi m z = pp m z := by
    intro m z hz
    have hlt : nsqZ (z + zz m) < nsqZ (zz m) := by
      rw [nsqZ_add]; omega
    exact hmin m (z + zz m) hlt
  have hne0 : ∀ m, chi m 0 ≠ pp m 0 := by
    intro m
    simpa [hchi, hpp] using hdef m
  -- `‖z_m‖₁ > m`.
  set ss : ℕ → ℤ := fun m => |(zz m).1| + |(zz m).2| with hss
  have hsm : ∀ m : ℕ, (m : ℤ) < ss m := by
    intro m
    by_contra hc
    push_neg at hc
    simp only [hss] at hc
    refine hdef m (hQ m (zz m) ?_)
    have h1 : |(zz m).1| ≤ (m : ℤ) := by
      have := abs_nonneg (zz m).2; omega
    have h2 : |(zz m).2| ≤ (m : ℤ) := by
      have := abs_nonneg (zz m).1; omega
    rw [abs_le] at h1 h2
    exact ⟨h1.1, h1.2, h2.1, h2.2⟩
  have hspos : ∀ m : ℕ, (0 : ℤ) < ss m := fun m => lt_of_le_of_lt (Int.ofNat_nonneg m) (hsm m)
  have hsR : ∀ m : ℕ, (0 : ℝ) < (ss m : ℝ) := fun m => by exact_mod_cast hspos m
  -- The normalised directions.
  set ee : ℕ → ℝ × ℝ :=
    fun m => ((-((zz m).1 : ℝ)) / (ss m : ℝ), (-((zz m).2 : ℝ)) / (ss m : ℝ)) with hee
  have heeinner : ∀ (m : ℕ) (z : ℤ × ℤ),
      inner2 (ee m) z = (-(dotZ z (zz m) : ℝ)) / (ss m : ℝ) := by
    intro m z
    simp only [hee, inner2, dotZ]
    push_cast
    field_simp
    ring
  have heeabs : ∀ m : ℕ, |(ee m).1| + |(ee m).2| = 1 := by
    intro m
    have hs := hsR m
    have key : ((ss m : ℤ) : ℝ) = |((zz m).1 : ℝ)| + |((zz m).2 : ℝ)| := by
      simp only [hss]
      push_cast
      ring
    simp only [hee, abs_div, abs_neg, abs_of_pos hs]
    field_simp
    linarith [key]
  have heebound : ∀ m : ℕ, (ee m).1 ∈ Set.Icc (-1 : ℝ) 1 ∧ (ee m).2 ∈ Set.Icc (-1 : ℝ) 1 := by
    intro m
    have h := heeabs m
    have h1 := abs_nonneg (ee m).1
    have h2 := abs_nonneg (ee m).2
    constructor
    · rw [Set.mem_Icc, ← abs_le]; linarith
    · rw [Set.mem_Icc, ← abs_le]; linarith
  -- A fixed ultrafilter refining `atTop`.
  set U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop with hU
  have hUle : (U : Filter ℕ) ≤ Filter.atTop := Ultrafilter.of_le _
  -- Limits of the two coordinates of the direction.
  obtain ⟨a1, -, ha1⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).ultrafilter_le_nhds
    (U.map fun m => (ee m).1)
    (by
      rw [le_principal_iff, Ultrafilter.coe_map, Filter.mem_map]
      exact Filter.univ_mem' fun k => (heebound k).1)
  obtain ⟨a2, -, ha2⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).ultrafilter_le_nhds
    (U.map fun m => (ee m).2)
    (by
      rw [le_principal_iff, Ultrafilter.coe_map, Filter.mem_map]
      exact Filter.univ_mem' fun k => (heebound k).2)
  have ht1 : Filter.Tendsto (fun m => (ee m).1) (U : Filter ℕ) (𝓝 a1) := by
    rw [Filter.Tendsto, ← Ultrafilter.coe_map]; exact ha1
  have ht2 : Filter.Tendsto (fun m => (ee m).2) (U : Filter ℕ) (𝓝 a2) := by
    rw [Filter.Tendsto, ← Ultrafilter.coe_map]; exact ha2
  set e : ℝ × ℝ := (a1, a2) with he
  -- The limit direction is a unit vector, in particular nonzero.
  have heunit : |a1| + |a2| = 1 := by
    have hlim : Filter.Tendsto (fun m => |(ee m).1| + |(ee m).2|) (U : Filter ℕ)
        (𝓝 (|a1| + |a2|)) := (ht1.abs).add (ht2.abs)
    have hconst : Filter.Tendsto (fun m => |(ee m).1| + |(ee m).2|) (U : Filter ℕ) (𝓝 1) := by
      have : (fun m => |(ee m).1| + |(ee m).2|) = fun _ : ℕ => (1 : ℝ) := funext heeabs
      rw [this]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hlim hconst
  have he0 : e ≠ 0 := by
    intro hc
    rw [Prod.ext_iff] at hc
    simp only [he, Prod.fst_zero, Prod.snd_zero] at hc
    rw [hc.1, hc.2] at heunit
    norm_num at heunit
  -- The pointwise limits.
  have hxr : Set.range x ⊆ Set.range ξ := by
    rintro - ⟨z, rfl⟩
    obtain ⟨u, hu⟩ := hx {z}
    exact ⟨u + z, (hu z (Finset.mem_singleton_self z)).symm⟩
  obtain ⟨chiL, hchiL⟩ := exists_ulimit hA U chi (fun m z => ⟨z + zz m + uu m, rfl⟩)
  obtain ⟨ppL, hppL⟩ := exists_ulimit hA U pp (fun m z => hxr ⟨z + zz m, rfl⟩)
  refine ⟨chiL, ppL, e, 1, ?_, ?_, ?_, he0, ?_, ?_⟩
  · -- `chiL ∈ X_ξ`
    refine orbitClosure_closed fun W => ?_
    obtain ⟨m, hm⟩ := Filter.nonempty_of_mem (hchiL W)
    exact ⟨chi m, hchiOC m, hm⟩
  · -- `ppL ∈ X_ξ`
    refine orbitClosure_closed fun W => ?_
    obtain ⟨m, hm⟩ := Filter.nonempty_of_mem (hppL W)
    exact ⟨pp m, hppOC m, hm⟩
  · -- `ppL` inherits all periods of `x`, hence is doubly periodic
    have hper : ∀ a, a ∈ Per x → a ∈ Per ppL := by
      intro a ha
      rw [mem_Per_iff]
      funext z
      show ppL (z + a) = ppL z
      obtain ⟨m, hm⟩ := Filter.nonempty_of_mem (hppL {z + a, z})
      have h1 : ppL (z + a) = pp m (z + a) := hm _ (by simp)
      have h2 : ppL z = pp m z := hm _ (by simp)
      rw [h1, h2]
      show x (z + a + zz m) = x (z + zz m)
      rw [show z + a + zz m = (z + zz m) + a by abel, Per.apply ha]
    obtain ⟨a, ha, b, hb, hdet⟩ := hxdp
    exact ⟨a, hper a ha, b, hper b hb, hdet⟩
  · -- disagreement at the origin
    obtain ⟨m, hm⟩ := Filter.nonempty_of_mem
      (Filter.inter_mem (hchiL {0}) (hppL {0}))
    have h1 : chiL 0 = chi m 0 := hm.1 _ (by simp)
    have h2 : ppL 0 = pp m 0 := hm.2 _ (by simp)
    rw [h1, h2]
    exact hne0 m
  · -- agreement on the half-plane `{1 ≤ ⟨z, e⟩}`
    intro z hz
    have hinner : Filter.Tendsto (fun m => inner2 (ee m) z) (U : Filter ℕ)
        (𝓝 (inner2 e z)) := by
      have : (fun m => inner2 (ee m) z)
          = fun m => (z.1 : ℝ) * (ee m).1 + (z.2 : ℝ) * (ee m).2 := by
        funext m; simp [inner2]
      rw [this]
      simpa only [he, inner2] using (ht1.const_mul ((z.1 : ℝ))).add (ht2.const_mul ((z.2 : ℝ)))
    have hcpos : (0 : ℝ) < inner2 e z / 2 := by linarith
    have hA1 : ∀ᶠ m in (U : Filter ℕ), inner2 e z / 2 < inner2 (ee m) z :=
      hinner.eventually_const_lt (by linarith)
    -- for large `m`, the ball is wide enough in the direction `z`
    obtain ⟨K, hK⟩ := exists_nat_gt ((nsqZ z : ℝ) / (2 * (inner2 e z / 2)))
    have hA2 : ∀ᶠ m in (U : Filter ℕ), (nsqZ z : ℝ) < 2 * (ss m : ℝ) * (inner2 e z / 2) := by
      have hbase : ∀ᶠ m in Filter.atTop,
          (nsqZ z : ℝ) < 2 * (ss m : ℝ) * (inner2 e z / 2) := by
        rw [Filter.eventually_atTop]
        refine ⟨K, fun m hm => ?_⟩
        have h1 : (K : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have h2 : (m : ℝ) < (ss m : ℝ) := by exact_mod_cast hsm m
        have h3 : (nsqZ z : ℝ) < (K : ℝ) * (2 * (inner2 e z / 2)) := by
          rw [div_lt_iff₀ (by linarith)] at hK; linarith
        nlinarith
      exact hUle hbase
    obtain ⟨m, ⟨⟨⟨hm1, hm2⟩, hm3⟩, hm4⟩⟩ := Filter.nonempty_of_mem
      (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hA1 hA2) (hchiL {z}))
        (hppL {z}))
    have hcond : nsqZ z < -2 * dotZ z (zz m) := by
      have hs := hsR m
      have hq1 : inner2 e z / 2 < inner2 (ee m) z := hm1
      have hq2 : (nsqZ z : ℝ) < 2 * (ss m : ℝ) * (inner2 e z / 2) := hm2
      have h1 : (nsqZ z : ℝ) < 2 * (ss m : ℝ) * inner2 (ee m) z := by nlinarith
      rw [heeinner m z] at h1
      have h2 : 2 * (ss m : ℝ) * (-(dotZ z (zz m) : ℝ) / (ss m : ℝ))
          = 2 * (-(dotZ z (zz m) : ℝ)) := by field_simp
      rw [h2] at h1
      have : (nsqZ z : ℝ) < ((-2 * dotZ z (zz m) : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have h1 : chiL z = chi m z := hm3 _ (by simp)
    have h2 : ppL z = pp m z := hm4 _ (by simp)
    rw [h1, h2]
    exact hball m z hcond

/-! ### Step 3 of Colle's proof of Theorem 1.14 -/

/-- **Step 3 of Colle's proof of Theorem 1.14.**

`exists_doublyPeriodic_in_orbitClosure` delivers a doubly periodic `x` in `X_ξ` (Colle's
`x_per`).  Theorem 1.14 claims `ξ` *itself* is doubly periodic.  Everything between the two is
this theorem: Colle §3.1 from the third paragraph on — Lemma 3.5, Claim 3.6, Claim 3.7 and a
second appeal to Boyle–Lind.

Note what is *not* assumed: `hONED` is kept, because the source uses the hypothesis again
after `x_per` is in hand — it is not consumed by step 2.  It is used exactly once below, and it
has to be: without it the statement is refuted by
`Nivat.KM.orbitClosure_doublyPeriodic_not_sufficient`.

The proof is the one described in this file's module docstring; it does not follow Colle's
route through the region combinatorics of Lemma 3.5. -/
theorem doublyPeriodic_of_orbitClosure_witness
    {ξ : Config ℤ} (hA : (Set.range ξ).Finite) (hann : HasNonzeroAnn ξ)
    (hONED : ∀ w : ℝ × ℝ, w ≠ 0 → ¬ (w ∈ ONED ξ ∧ -w ∈ ONED ξ))
    {x : Config ℤ} (hx : x ∈ orbitClosure ξ) (hxdp : DoublyPeriodic x) :
    DoublyPeriodic ξ := by
  classical
  by_contra hnd
  -- Kari–Szabados: a product-of-shifts annihilator with pairwise non-parallel directions.
  obtain ⟨n, h, -, hne, hnp, hφ⟩ := Nivat.KSC.kari_szabados_prodShift' hA hann
  -- The nearest-defect construction.
  obtain ⟨chi, p, e, c, hchiOC, hpOC, hpdp, he0, hne0, hagree⟩ :=
    exists_halfPlane_disagreement hA hx hxdp hnd
  have hchiann : act (∏ i, (mono (h i) - 1) : LaurentTwo ℤ) chi = 0 :=
    act_eq_zero_of_mem_orbitClosure hφ hchiOC
  have hpann : act (∏ i, (mono (h i) - 1) : LaurentTwo ℤ) p = 0 :=
    act_eq_zero_of_mem_orbitClosure hφ hpOC
  have hchine : chi ≠ p := fun hc => hne0 (by rw [hc])
  -- Colle Lemma 2.6: the limit direction is orthogonal to one of the `hᵢ`.
  have hperp : ∃ i, inner2 e (h i) = 0 := by
    by_contra hc
    push_neg at hc
    exact hchine (eq_of_agree_halfPlane_of_transverse hne hnp hchiann hpann hc hagree)
  obtain ⟨i, hi⟩ := hperp
  -- A multiple of `h i` that is a period of `p`, tangent to the half-plane.
  obtain ⟨N, hN, hNp⟩ := hpdp.exists_smul_mem
  set u : ℤ × ℤ := N • h i with hu
  have hu0 : u ≠ 0 := smul_ne_zero hN (hne i)
  have hue : inner2 e u = 0 := by rw [hu, inner2_zsmul, hi, mul_zero]
  have huPer : u ∈ Per p := hNp (h i)
  -- `chi` is `u`-periodic on the half-plane.
  have hlocal : ∀ z, c ≤ inner2 e z → chi (z + u) = chi z := by
    intro z hz
    have hz' : c ≤ inner2 e (z + u) := by rw [inner2_add, hue, add_zero]; exact hz
    rw [hagree (z + u) hz', hagree z hz, Per.apply huPer]
  -- Proposition 2.12 upgrades this to a global period.
  obtain ⟨f, hfp, hfsum⟩ := kari_szabados_decomp' hne hnp hchiann
  have hchieq : (fun z => ∑ i, f i z) = chi := funext fun z => (hfsum z).symm
  obtain ⟨k, hk, hkPer⟩ := exists_period_multiple_of_halfPlane (A := ℤ) Finset.univ f h
    (w := e) he0 (c := c) hu0 hue (fun i _ => hfp i) (fun i _ => hne i)
    (by
      intro z hz
      rw [← hfsum (z + u), ← hfsum z]
      exact hlocal z hz)
  rw [hchieq] at hkPer
  -- Proposition 1.8 / Boyle–Lind: a periodic member of `X_ξ` is doubly periodic.
  -- This is the only use of `hONED`.
  have hchidp : DoublyPeriodic chi :=
    Nivat.Colle3.doublyPeriodic_of_isPeriodic hA hONED hchiOC ⟨k • u, hkPer, smul_ne_zero hk hu0⟩
  -- A common period pointing into the half-plane forces equality.
  obtain ⟨N1, hN1, hN1p⟩ := hchidp.exists_smul_mem
  obtain ⟨N2, hN2, hN2p⟩ := hpdp.exists_smul_mem
  obtain ⟨a, ha⟩ : ∃ a : ℤ × ℤ, inner2 e a ≠ 0 := by
    by_cases h1 : e.1 = 0
    · refine ⟨(0, 1), ?_⟩
      simp only [inner2]
      have : e.2 ≠ 0 := by
        intro h2
        exact he0 (Prod.ext h1 h2)
      simpa using this
    · refine ⟨(1, 0), ?_⟩
      simp only [inner2]
      simpa using h1
  obtain ⟨q, hqchi, hqp, hqpos⟩ :
      ∃ q : ℤ × ℤ, q ∈ Per chi ∧ q ∈ Per p ∧ 0 < inner2 e q := by
    have hmem : ∀ b : ℤ × ℤ, (N1 * N2) • b ∈ Per chi ∧ (N1 * N2) • b ∈ Per p := by
      intro b
      constructor
      · rw [mul_smul]; exact hN1p _
      · rw [mul_comm, mul_smul]; exact hN2p _
    have hval : ∀ b : ℤ × ℤ, inner2 e ((N1 * N2) • b) = ((N1 * N2 : ℤ) : ℝ) * inner2 e b := by
      intro b; rw [inner2_zsmul]
    rcases lt_trichotomy (inner2 e ((N1 * N2) • a)) 0 with hlt | heq | hgt
    · exact ⟨-((N1 * N2) • a), neg_mem (hmem a).1, neg_mem (hmem a).2, by
        rw [inner2_neg]; linarith⟩
    · exfalso
      rw [hval a] at heq
      rcases mul_eq_zero.mp heq with h1 | h1
      · exact (mul_ne_zero hN1 hN2) (by exact_mod_cast h1)
      · exact ha h1
    · exact ⟨(N1 * N2) • a, (hmem a).1, (hmem a).2, hgt⟩
  have hEq : chi = p := by
    funext z
    obtain ⟨M, hM⟩ := exists_nat_gt ((c - inner2 e z) / inner2 e q)
    have hlt : c - inner2 e z < (M : ℝ) * inner2 e q := (div_lt_iff₀ hqpos).mp hM
    have hz : c ≤ inner2 e (z + (M : ℤ) • q) := by
      rw [inner2_add, inner2_zsmul]
      push_cast
      linarith
    have h1 : chi (z + (M : ℤ) • q) = chi z := Per.apply ((Per chi).zsmul_mem hqchi (M : ℤ)) z
    have h2 : p (z + (M : ℤ) • q) = p z := Per.apply ((Per p).zsmul_mem hqp (M : ℤ)) z
    rw [← h1, ← h2]
    exact hagree _ hz
  exact hne0 (by rw [hEq])

/-- **Colle, Theorem 1.14.**

The signature is character-for-character the one carried by the axiom
`Nivat.colle_doublyPeriodic` in `Nivat/Section8/External.lean`.

## Correction, 2026-09-16: this docstring used to say step 2 still carries `sorryAx`

It said *"the remaining `sorryAx` comes from step 2 (`exists_doublyPeriodic_in_orbitClosure`,
via `Nivat.KM17.lemma17`)"*.  **That is stale, and it has already misled one reader into
reporting `exists_chainData` as blocked by this theorem.**

The dependency was rewired on 2026-09-14 (commits `4b0d9ed`, `6ac85a3`).  `theorem114` no
longer reaches `Nivat.KM17.lemma17`, and `Nivat.colle_doublyPeriodic` left the closure of
`Nivat.nivat_conjecture` at the `2026-09-13T19:14` entry of `blueprint/GATE_LOG.jsonl` — it
is discharged in `Nivat/Section8/ExternalDischarged.lean` via `exists_mem_ONED'`.
`KMLemma17.lean`'s `lemma17` is now dead code with respect to this path.

Measure rather than read: `#print axioms Nivat.Colle.theorem114`. -/
theorem theorem114 {ξ : Config ℤ} (hA : (Set.range ξ).Finite) (hann : HasNonzeroAnn ξ)
    (hONED : ∀ w : ℝ × ℝ, w ≠ 0 → ¬ (w ∈ ONED ξ ∧ -w ∈ ONED ξ)) :
    DoublyPeriodic ξ :=
  let ⟨_x, hx, hxdp⟩ := exists_doublyPeriodic_in_orbitClosure hA hann hONED
  doublyPeriodic_of_orbitClosure_witness hA hann hONED hx hxdp

end Nivat.Colle
