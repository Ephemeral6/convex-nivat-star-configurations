/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges

/-!
# Edges of infinite lattice-convex regions

This file closes three gaps left open by `Nivat/External/Colle/LatticeEdges.lean`
(see its `Status` section) in the formalisation of

Cleber F. Colle, *On periodic decompositions, one-sided nonexpansive directions and
Nivat's conjecture*, arXiv:1909.08195**v4**, §2.1, §3, §4.

Colle, **Definition 3.1** (v4, §3), verbatim:

> Let `ℓ, ℓ' ⊂ ℝ²` be rational oriented lines in distinct directions.  A convex set
> `ℛ ⊂ ℤ²` (positively oriented) with two semi-infinite edges parallels to `ℓ` and
> `ℓ'`, respectively, is called an `(ℓ,ℓ')`-region if `w ≺ ⋯ ≺ w'`, where
> `w ∈ E(ℛ)` is the edge parallel to `ℓ` and `w' ∈ E(ℛ)` is the edge parallel to
> `ℓ'`.
>
> In the previous definition, `w ≺ ⋯ ≺ w'` means that, following the orientation of
> `ℛ`, the edge of `ℛ` parallel to `ℓ` comes first than the edge of `ℛ` parallel to
> `ℓ'`.

`LatticeEdges.lean` had to put *both* "`|E(ℛ)| < ∞`" and "`w ≺ ⋯ ≺ w'`" into the
structure `IsRegion` as **fields**.  The main results here turn both into theorems:

* `Nivat.LE2.finite_E_of_two_semiInf` — a set with two semi-infinite edges in
  non-(anti)parallel directions has **finitely many edges**;
* `Nivat.LE2.precedesAll_of_two_semiInf` — and its edge set is exactly a
  **cyclic-order interval** from one semi-infinite edge to the other;
* `Nivat.LE2.isRegion_of_two_semiInf` — hence `IsRegion` can be built from data that
  no longer mentions `edgesFinite` or `precedes`.

Both are proved with **no convexity hypothesis at all**: only that the two
distinguished faces are infinite.  The mechanism is the elementary identity

  `det n n' * ⟨m, z⟩ = det m n' * ⟨n, z⟩ + det n m * ⟨n', z⟩`     (`cramer_dot`)

which expresses every direction `m` in the basis `{n, n'}`, together with the
observation that an infinite face is unbounded, so that `⟨n', ·⟩` takes arbitrarily
negative values on `face R n`.

The third gap — the behaviour of `E(·)` under intersection with a half-plane
`ℋ(ℓ)`, needed by Colle's Claim 3.7 and Lemma 4.1 — is only **partly** closed here;
in particular §6 contains a *counterexample* showing that the naive statement
`E(𝒮 ∩ ℋ) ⊆ E(𝒮) ∪ {ℓ}` is **false**, even for a lattice box.  See the `Status`
section at the end for the exact score.

Sign conventions are those of `LatticeEdges.lean` (outer normals, maximal faces).
-/

namespace Nivat.LE2

open Nivat

variable {R : Set (ℤ × ℤ)} {n n' m a a' : ℤ × ℤ}

/-! ## §1. Two-dimensional linear algebra over `ℤ`

Everything in this section is an identity between integer polynomials; nothing is
assumed about `R`. -/

/-- **Cramer's rule in `ℤ²`.**  If `det n n' ≠ 0` then `{n, n'}` is a basis of `ℚ²`
and `det n n' • m = (det m n') • n + (det n m) • n'`.  Pairing with `z` gives this
identity, which holds unconditionally. -/
theorem cramer_dot (n n' m z : ℤ × ℤ) :
    det n n' * dot m z = det m n' * dot n z + det n m * dot n' z := by
  simp only [det, dot]; ring

/-- The vector form of `cramer_dot`, first coordinate. -/
theorem cramer_fst (n n' m : ℤ × ℤ) :
    det n n' * m.1 = det m n' * n.1 + det n m * n'.1 := by
  simp only [det]; ring

/-- The vector form of `cramer_dot`, second coordinate. -/
theorem cramer_snd (n n' m : ℤ × ℤ) :
    det n n' * m.2 = det m n' * n.2 + det n m * n'.2 := by
  simp only [det]; ring

theorem det_neg_right (u v : ℤ × ℤ) : det u (-v) = -det u v := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

theorem det_neg_left (u v : ℤ × ℤ) : det (-u) v = -det u v := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

/-- Two independent linear forms separate points of `ℤ²`. -/
theorem eq_of_dot_eq_dot {n n' z w : ℤ × ℤ} (hD : det n n' ≠ 0)
    (h1 : dot n z = dot n w) (h2 : dot n' z = dot n' w) : z = w := by
  simp only [dot] at h1 h2
  have e1 : det n n' * (z.1 - w.1) = 0 := by
    simp only [det]; linear_combination n'.2 * h1 - n.2 * h2
  have e2 : det n n' * (z.2 - w.2) = 0 := by
    simp only [det]; linear_combination (-n'.1) * h1 + n.1 * h2
  have f1 : z.1 = w.1 := by
    rcases mul_eq_zero.mp e1 with h | h
    · exact absurd h hD
    · omega
  have f2 : z.2 = w.2 := by
    rcases mul_eq_zero.mp e2 with h | h
    · exact absurd h hD
    · omega
  exact Prod.ext f1 f2

/-- **A lattice "box" in two independent linear forms is finite.**  This is the only
finiteness input of the whole file. -/
theorem finite_of_dot_bounded {n n' : ℤ × ℤ} (hD : det n n' ≠ 0) (p q p' q' : ℤ) :
    {z : ℤ × ℤ | p ≤ dot n z ∧ dot n z ≤ q ∧ p' ≤ dot n' z ∧ dot n' z ≤ q'}.Finite := by
  have hinj : Set.InjOn (fun z : ℤ × ℤ => (dot n z, dot n' z))
      {z : ℤ × ℤ | p ≤ dot n z ∧ dot n z ≤ q ∧ p' ≤ dot n' z ∧ dot n' z ≤ q'} := by
    intro x _ y _ h
    exact eq_of_dot_eq_dot hD (congrArg Prod.fst h) (congrArg Prod.snd h)
  refine Set.Finite.of_finite_image ?_ hinj
  refine Set.Finite.subset ((Set.finite_Icc p q).prod (Set.finite_Icc p' q')) ?_
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨⟨hz.1, hz.2.1⟩, ⟨hz.2.2.1, hz.2.2.2⟩⟩

/-- If `B * s ≤ K` for arbitrarily negative integers `s`, then `0 ≤ B`. -/
theorem nonneg_of_bounded_on_unbounded_below {B K : ℤ}
    (h : ∀ N : ℤ, ∃ s : ℤ, s < N ∧ B * s ≤ K) : 0 ≤ B := by
  by_contra hB
  push Not at hB
  obtain ⟨s, hs1, hs2⟩ := h (min 0 (-K))
  have h1 : s < 0 := lt_of_lt_of_le hs1 (min_le_left _ _)
  have h2 : s < -K := lt_of_lt_of_le hs1 (min_le_right _ _)
  have key : 0 ≤ (-s) * (-B - 1) := mul_nonneg (by omega) (by omega)
  nlinarith [key]

/-! ## §2. An infinite face is unbounded

If `face R n` is infinite and a second independent direction `n'` is bounded above on
`R`, then `⟨n', ·⟩` takes arbitrarily negative values on `face R n`: the face runs off
to infinity, and it can only do so *away* from the half-plane `{⟨n',·⟩ ≤ c'}`.

No convexity is used: `⟨n, ·⟩` is constant on `face R n` (`dot_eq_of_mem_face`), so a
two-sided bound on `⟨n', ·⟩` would confine the face to a finite box. -/

/-- **An infinite face escapes to `-∞` in every transverse direction bounded above.** -/
theorem exists_dot_lt_of_infinite_face {R : Set (ℤ × ℤ)} {n n' : ℤ × ℤ}
    (hD : det n n' ≠ 0) (hinf : (face R n).Infinite) {c' : ℤ}
    (hb : ∀ z ∈ R, dot n' z ≤ c') (N : ℤ) : ∃ z ∈ face R n, dot n' z < N := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha⟩ := hinf.nonempty
  refine hinf (Set.Finite.subset (finite_of_dot_bounded hD (dot n a) (dot n a) N c') ?_)
  intro z hz
  refine ⟨le_of_eq (dot_eq_of_mem_face ha hz), le_of_eq (dot_eq_of_mem_face hz ha),
    hcon z hz, hb z hz.1⟩

/-! ## §3. The cone of admissible edge directions

Fix two semi-infinite edges `n`, `n'` with `0 < det n n'` (i.e. `n'` is reached from
`n` by a counter-clockwise turn of less than `π`).  Writing, for an arbitrary
direction `m`,

  `A := det m n'`,  `B := det n m`,  `D := det n n' > 0`,

Cramer's rule reads `D • m = A • n + B • n'`.  The results of this section say:

* every direction with a non-empty face has `A ≥ 0` and `B ≥ 0` — the *dual cone*
  condition (`det_nonneg_of_semiInf`);
* `A = 0` forces `m = n'` and `B = 0` forces `m = n` (`eq_right_of_det_eq_zero`,
  `eq_left_of_det_eq_zero`);
* all remaining directions have their whole face inside one fixed finite box
  (`face_subset_box`).

Together: apart from `n` and `n'` themselves, all edges of `R` live in a finite box. -/

/-- **The dual-cone condition.**  If `n` and `n'` carry infinite faces and
`0 < det n n'`, then every direction `m` whose face is non-empty satisfies
`0 ≤ det n m` and `0 ≤ det m n'`. -/
theorem det_nonneg_of_semiInf {R : Set (ℤ × ℤ)} {n n' m : ℤ × ℤ} (hD : 0 < det n n')
    (hinf : (face R n).Infinite) (hinf' : (face R n').Infinite)
    (hne : (face R m).Nonempty) : 0 ≤ det n m ∧ 0 ≤ det m n' := by
  obtain ⟨w, hw⟩ := hne
  obtain ⟨a, ha⟩ := hinf.nonempty
  obtain ⟨a', ha'⟩ := hinf'.nonempty
  have hbn : ∀ z ∈ R, dot n z ≤ dot n a := fun z hz => ha.2 z hz
  have hbn' : ∀ z ∈ R, dot n' z ≤ dot n' a' := fun z hz => ha'.2 z hz
  have hDne : det n n' ≠ 0 := hD.ne'
  have hDne' : det n' n ≠ 0 := by
    intro h
    apply hDne
    have : det n' n = -det n n' := by simp only [det]; ring
    omega
  constructor
  · -- `0 ≤ det n m`
    refine nonneg_of_bounded_on_unbounded_below
      (K := det n n' * dot m w - det m n' * dot n a) (fun N => ?_)
    obtain ⟨z, hz, hlt⟩ := exists_dot_lt_of_infinite_face hDne hinf hbn' N
    refine ⟨dot n' z, hlt, ?_⟩
    have h1 : dot m z ≤ dot m w := hw.2 z hz.1
    have h2 : det n n' * dot m z ≤ det n n' * dot m w :=
      mul_le_mul_of_nonneg_left h1 hD.le
    have h3 := cramer_dot n n' m z
    have h4 : dot n z = dot n a := dot_eq_of_mem_face hz ha
    rw [h4] at h3
    omega
  · -- `0 ≤ det m n'`
    refine nonneg_of_bounded_on_unbounded_below
      (K := det n n' * dot m w - det n m * dot n' a') (fun N => ?_)
    obtain ⟨z, hz, hlt⟩ := exists_dot_lt_of_infinite_face hDne' hinf' hbn N
    refine ⟨dot n z, hlt, ?_⟩
    have h1 : dot m z ≤ dot m w := hw.2 z hz.1
    have h2 : det n n' * dot m z ≤ det n n' * dot m w :=
      mul_le_mul_of_nonneg_left h1 hD.le
    have h3 := cramer_dot n n' m z
    have h4 : dot n' z = dot n' a' := dot_eq_of_mem_face hz ha'
    rw [h4] at h3
    omega

/-- On the boundary ray `det m n' = 0` of the dual cone the only primitive direction
is `n'` itself. -/
theorem eq_right_of_det_eq_zero {n n' m : ℤ × ℤ} (hD : 0 < det n n') (hm : Prim m)
    (hn' : Prim n') (hB : 0 ≤ det n m) (hA : det m n' = 0) : m = n' := by
  rcases eq_or_neg_of_prim_of_det_eq_zero hm hn' hA with h | h
  · exact h.symm
  · exfalso
    have : det n n' = -det n m := by rw [h, det_neg_right]
    omega

/-- On the boundary ray `det n m = 0` of the dual cone the only primitive direction
is `n` itself. -/
theorem eq_left_of_det_eq_zero {n n' m : ℤ × ℤ} (hD : 0 < det n n') (hn : Prim n)
    (hm : Prim m) (hA : 0 ≤ det m n') (hB : det n m = 0) : m = n := by
  rcases eq_or_neg_of_prim_of_det_eq_zero hn hm hB with h | h
  · exact h
  · exfalso
    have : det m n' = -det n n' := by rw [h]; rw [det_neg_left]
    omega

/-- **The interior directions have short faces.**  If `m` is strictly inside the cone
spanned by `n` and `n'` then `face R m` lies in the box cut out by the four support
levels of `n` and `n'`, hence (`finite_of_dot_bounded`) in a finite set. -/
theorem face_subset_box {R : Set (ℤ × ℤ)} {n n' m a a' : ℤ × ℤ}
    (ha : a ∈ face R n) (ha' : a' ∈ face R n')
    (hA : 0 < det m n') (hB : 0 < det n m) (hD : 0 < det n n') :
    face R m ⊆ {z : ℤ × ℤ | dot n a' ≤ dot n z ∧ dot n z ≤ dot n a ∧
      dot n' a ≤ dot n' z ∧ dot n' z ≤ dot n' a'} := by
  intro z hz
  have hzR : z ∈ R := hz.1
  have hup : dot n z ≤ dot n a := ha.2 z hzR
  have hup' : dot n' z ≤ dot n' a' := ha'.2 z hzR
  have hcz := cramer_dot n n' m z
  refine ⟨?_, hup, ?_, hup'⟩
  · -- `dot n a' ≤ dot n z`
    by_contra hc
    push Not at hc
    have hca' := cramer_dot n n' m a'
    have h1 : dot m a' ≤ dot m z := hz.2 a' ha'.1
    have h2 : det n n' * dot m a' ≤ det n n' * dot m z :=
      mul_le_mul_of_nonneg_left h1 hD.le
    have h3 : det n m * dot n' z ≤ det n m * dot n' a' :=
      mul_le_mul_of_nonneg_left hup' hB.le
    have h4 : det m n' * dot n z < det m n' * dot n a' := mul_lt_mul_of_pos_left hc hA
    omega
  · -- `dot n' a ≤ dot n' z`
    by_contra hc
    push Not at hc
    have hca := cramer_dot n n' m a
    have h1 : dot m a ≤ dot m z := hz.2 a ha.1
    have h2 : det n n' * dot m a ≤ det n n' * dot m z :=
      mul_le_mul_of_nonneg_left h1 hD.le
    have h3 : det m n' * dot n z ≤ det m n' * dot n a :=
      mul_le_mul_of_nonneg_left hup hA.le
    have h4 : det n m * dot n' z < det n m * dot n' a := mul_lt_mul_of_pos_left hc hB
    omega

/-! ## §4. Gap 1: an `(ℓ,ℓ')`-region has finitely many edges -/

theorem ne_of_det_pos {n n' : ℤ × ℤ} (hD : 0 < det n n') : n' ≠ n ∧ n' ≠ -n := by
  constructor
  · rintro rfl; rw [det_self] at hD; exact absurd hD (lt_irrefl 0)
  · rintro rfl; rw [det_neg_right, det_self] at hD; omega

/-- **Gap 1, closed.**  A set with two semi-infinite edges whose outer normals are not
(anti)parallel has only finitely many edges.

This is Colle's standing requirement "`|E(ℛ)| < ∞`" for an `(ℓ,ℓ')`-region
(Definition 3.1 together with §2.1), which `LatticeEdges.lean` could only assume
(field `IsRegion.edgesFinite`).  Note that **no convexity or closedness hypothesis is
needed**; two non-parallel semi-infinite edges suffice. -/
theorem finite_E_of_two_semiInf {R : Set (ℤ × ℤ)} {n n' : ℤ × ℤ}
    (hn : IsSemiInfEdge R n) (hn' : IsSemiInfEdge R n') (hD : 0 < det n n') :
    (E R).Finite := by
  obtain ⟨hnE, hinf⟩ := hn
  obtain ⟨hn'E, hinf'⟩ := hn'
  obtain ⟨hne1, hne2⟩ := ne_of_det_pos hD
  have hpos : PosArea R := posArea_of_edges hnE hn'E hne1 hne2
  obtain ⟨a, ha⟩ := hinf.nonempty
  obtain ⟨a', ha'⟩ := hinf'.nonempty
  set Box : Set (ℤ × ℤ) := {z : ℤ × ℤ | dot n a' ≤ dot n z ∧ dot n z ≤ dot n a ∧
      dot n' a ≤ dot n' z ∧ dot n' z ≤ dot n' a'} with hBox
  have hBoxFin : Box.Finite := finite_of_dot_bounded hD.ne' _ _ _ _
  have hS : {k | k ∈ E R ∧ face R k ⊆ Box}.Finite := by
    refine Set.Finite.of_finite_image ?_ ((injOn_face hpos).mono (fun k hk => hk.1))
    refine Set.Finite.subset hBoxFin.finite_subsets ?_
    rintro _ ⟨k, hk, rfl⟩
    exact hk.2
  refine Set.Finite.subset (((hS.insert n').insert n)) ?_
  intro k hk
  by_cases h1 : k = n
  · exact Set.mem_insert_iff.mpr (Or.inl h1)
  by_cases h2 : k = n'
  · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_insert_iff.mpr (Or.inl h2)))
  refine Set.mem_insert_iff.mpr (Or.inr (Set.mem_insert_iff.mpr (Or.inr ⟨hk, ?_⟩)))
  obtain ⟨x, hx, -, -, -⟩ := hk.2
  obtain ⟨hB, hA⟩ := det_nonneg_of_semiInf hD hinf hinf' ⟨x, hx⟩
  have hA0 : det k n' ≠ 0 := fun h => h2 (eq_right_of_det_eq_zero hD hk.1 hn'E.1 hB h)
  have hB0 : det n k ≠ 0 := fun h => h1 (eq_left_of_det_eq_zero hD hnE.1 hk.1 hA h)
  exact face_subset_box ha ha' (lt_of_le_of_ne hA (Ne.symm hA0))
    (lt_of_le_of_ne hB (Ne.symm hB0)) hD

/-! ## §5. The angular order is the sign of the determinant

`LatticeEdges.lean` defines the counter-clockwise order `angLT` through the key
`angKey = (half, angSlope)`.  To connect it with the cone computations of §3 we need
the standard dictionary

  `angLT a b ↔ half a < half b ∨ (half a = half b ∧ 0 < det a b)`

(`angLT_iff_det`).  Nothing here refers to a set `R`. -/

theorem half_cases (a : ℤ × ℤ) : half a = 0 ∨ half a = 1 := by
  unfold half
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem half_eq_zero_iff {a : ℤ × ℤ} : half a = 0 ↔ (0 < a.2 ∨ (a.2 = 0 ∧ 0 < a.1)) := by
  unfold half; split <;> simp_all

theorem half_eq_one_iff {a : ℤ × ℤ} :
    half a = 1 ↔ ¬(0 < a.2 ∨ (a.2 = 0 ∧ 0 < a.1)) := by
  unfold half; split <;> simp_all

/-- The rational cross-multiplication behind `angSlope`. -/
theorem neg_div_lt_neg_div_iff {p q r s : ℤ} (h : 0 < q * s) :
    (-(p : ℚ)) / (q : ℚ) < (-(r : ℚ)) / (s : ℚ) ↔ 0 < p * s - q * r := by
  have hq : q ≠ 0 := by rintro rfl; simp at h
  have hs : s ≠ 0 := by rintro rfl; simp at h
  have hqQ : ((q : ℚ)) ≠ 0 := Int.cast_ne_zero.mpr hq
  have hsQ : ((s : ℚ)) ≠ 0 := Int.cast_ne_zero.mpr hs
  have hprod : (0 : ℚ) < (q : ℚ) * (s : ℚ) := by exact_mod_cast h
  rw [← sub_pos]
  have key : (-(r : ℚ)) / (s : ℚ) - (-(p : ℚ)) / (q : ℚ)
      = ((p * s - q * r : ℤ) : ℚ) / ((q : ℚ) * (s : ℚ)) := by
    push_cast
    field_simp
    ring
  rw [key, div_pos_iff]
  constructor
  · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
    · exact_mod_cast h1
    · exact absurd h2 (not_lt.mpr hprod.le)
  · intro h1
    exact Or.inl ⟨by exact_mod_cast h1, hprod⟩

/-- **Within one half-plane of directions, the angular order is the sign of the
determinant.** -/
theorem angSlope_lt_iff_det {a b : ℤ × ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hh : half a = half b) : angSlope a < angSlope b ↔ 0 < det a b := by
  have hane : a.1 ≠ 0 ∨ a.2 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact ha (Prod.ext hc.1 hc.2)
  have hbne : b.1 ≠ 0 ∨ b.2 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hb (Prod.ext hc.1 hc.2)
  by_cases ha2 : a.2 = 0
  · by_cases hb2 : b.2 = 0
    · rw [angSlope, angSlope, if_pos ha2, if_pos hb2]
      simp only [lt_self_iff_false, det, ha2, hb2, mul_zero, zero_mul, sub_self,
        lt_self_iff_false]
    · rw [angSlope, angSlope, if_pos ha2, if_neg hb2]
      simp only [WithBot.bot_lt_coe, true_iff, det, ha2, zero_mul, sub_zero]
      have ha1 : a.1 ≠ 0 := by rcases hane with h | h; exacts [h, absurd ha2 h]
      rcases half_cases a with h0 | h1
      · have hb0 : half b = 0 := by omega
        have t1 : 0 < a.1 := by have := half_eq_zero_iff.mp h0; omega
        have t2 : 0 < b.2 := by have := half_eq_zero_iff.mp hb0; omega
        exact mul_pos t1 t2
      · have hb1 : half b = 1 := by omega
        have t1 : a.1 < 0 := by have := half_eq_one_iff.mp h1; omega
        have t2 : b.2 < 0 := by have := half_eq_one_iff.mp hb1; omega
        exact mul_pos_of_neg_of_neg t1 t2
  · by_cases hb2 : b.2 = 0
    · rw [angSlope, angSlope, if_neg ha2, if_pos hb2]
      simp only [not_lt_bot, false_iff, det, hb2, mul_zero, zero_sub, not_lt, neg_nonpos]
      have hb1' : b.1 ≠ 0 := by rcases hbne with h | h; exacts [h, absurd hb2 h]
      rcases half_cases a with h0 | h1
      · have hb0 : half b = 0 := by omega
        have t1 : 0 < a.2 := by have := half_eq_zero_iff.mp h0; omega
        have t2 : 0 < b.1 := by have := half_eq_zero_iff.mp hb0; omega
        exact (mul_pos t1 t2).le
      · have hb1 : half b = 1 := by omega
        have t1 : a.2 < 0 := by have := half_eq_one_iff.mp h1; omega
        have t2 : b.1 < 0 := by have := half_eq_one_iff.mp hb1; omega
        exact (mul_pos_of_neg_of_neg t1 t2).le
    · rw [angSlope, angSlope, if_neg ha2, if_neg hb2, WithBot.coe_lt_coe]
      have hqs : 0 < a.2 * b.2 := by
        rcases half_cases a with h0 | h1
        · have hb0 : half b = 0 := by omega
          have t1 : 0 < a.2 := by have := half_eq_zero_iff.mp h0; omega
          have t2 : 0 < b.2 := by have := half_eq_zero_iff.mp hb0; omega
          exact mul_pos t1 t2
        · have hb1 : half b = 1 := by omega
          have t1 : a.2 < 0 := by have := half_eq_one_iff.mp h1; omega
          have t2 : b.2 < 0 := by have := half_eq_one_iff.mp hb1; omega
          exact mul_pos_of_neg_of_neg t1 t2
      rw [neg_div_lt_neg_div_iff hqs]
      simp only [det]

/-- **The dictionary between the counter-clockwise order and the determinant.** -/
theorem angLT_iff_det {a b : ℤ × ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    angLT a b ↔ half a < half b ∨ (half a = half b ∧ 0 < det a b) := by
  rw [angLT_iff]
  constructor
  · rintro (h | ⟨h, hs⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h, (angSlope_lt_iff_det ha hb h).mp hs⟩
  · rintro (h | ⟨h, hs⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h, (angSlope_lt_iff_det ha hb h).mpr hs⟩

theorem angLT_iff_half_le {a b : ℤ × ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (h : 0 < det a b) :
    angLT a b ↔ half a ≤ half b := by
  rw [angLT_iff_det ha hb]
  constructor
  · rintro (h1 | ⟨h1, -⟩) <;> omega
  · intro h1
    rcases lt_or_eq_of_le h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr ⟨h2, h⟩

theorem angLT_iff_half_lt {a b : ℤ × ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (h : det a b ≤ 0) :
    angLT a b ↔ half a < half b := by
  rw [angLT_iff_det ha hb]
  constructor
  · rintro (h1 | ⟨-, h2⟩)
    · exact h1
    · omega
  · exact Or.inl

/-- **A direction strictly inside the cone `⟨n, n'⟩` lies in the same half-plane as
its two generators.**  This is what rules out the "impossible" half-patterns in
`cycBtw_of_cone`. -/
theorem half_eq_of_cone {n n' m : ℤ × ℤ} (hD : 0 < det n n')
    (hA : 0 < det m n') (hB : 0 < det n m) (hh : half n = half n') : half m = half n := by
  have hc := cramer_snd n n' m
  rcases half_cases n with h0 | h1
  · have h0' : half n' = 0 := by omega
    have e1 : 0 ≤ n.2 := by have := half_eq_zero_iff.mp h0; omega
    have e2 : 0 ≤ n'.2 := by have := half_eq_zero_iff.mp h0'; omega
    have t1 : 0 ≤ det m n' * n.2 := mul_nonneg hA.le e1
    have t2 : 0 ≤ det n m * n'.2 := mul_nonneg hB.le e2
    have hm2 : 0 ≤ det n n' * m.2 := by omega
    have hm2' : 0 ≤ m.2 := by
      by_contra hcon
      push Not at hcon
      nlinarith
    rcases lt_or_eq_of_le hm2' with hlt | heq
    · rw [h0]; exact half_eq_zero_iff.mpr (Or.inl hlt)
    · exfalso
      have hz : det n n' * m.2 = 0 := by rw [← heq, mul_zero]
      have h3 : det m n' * n.2 = 0 := by omega
      have h4 : det n m * n'.2 = 0 := by omega
      have hn2 : n.2 = 0 := by
        rcases mul_eq_zero.mp h3 with h | h
        exacts [absurd h hA.ne', h]
      have hn'2 : n'.2 = 0 := by
        rcases mul_eq_zero.mp h4 with h | h
        exacts [absurd h hB.ne', h]
      have : det n n' = 0 := by simp only [det, hn2, hn'2]; ring
      omega
  · have h1' : half n' = 1 := by omega
    have e1 : n.2 ≤ 0 := by have := half_eq_one_iff.mp h1; omega
    have e2 : n'.2 ≤ 0 := by have := half_eq_one_iff.mp h1'; omega
    have t1 : det m n' * n.2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hA.le e1
    have t2 : det n m * n'.2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hB.le e2
    have hm2 : det n n' * m.2 ≤ 0 := by omega
    have hm2' : m.2 ≤ 0 := by
      by_contra hcon
      push Not at hcon
      nlinarith
    rcases lt_or_eq_of_le hm2' with hlt | heq
    · rw [h1]; exact half_eq_one_iff.mpr (by omega)
    · exfalso
      have hz : det n n' * m.2 = 0 := by rw [heq, mul_zero]
      have h3 : det m n' * n.2 = 0 := by omega
      have h4 : det n m * n'.2 = 0 := by omega
      have hn2 : n.2 = 0 := by
        rcases mul_eq_zero.mp h3 with h | h
        exacts [absurd h hA.ne', h]
      have hn'2 : n'.2 = 0 := by
        rcases mul_eq_zero.mp h4 with h | h
        exacts [absurd h hB.ne', h]
      have : det n n' = 0 := by simp only [det, hn2, hn'2]; ring
      omega

/-- **Strictly inside the cone implies strictly between in the cyclic order.**  This
is the geometric heart of Colle's `w ≺ ⋯ ≺ w'`. -/
theorem cycBtw_of_cone {n m n' : ℤ × ℤ} (hn : n ≠ 0) (hm : m ≠ 0) (hn' : n' ≠ 0)
    (hB : 0 < det n m) (hA : 0 < det m n') (hD : 0 < det n n') : CycBtw n m n' := by
  have hL2 : half n = half n' → half m = half n := fun h => half_eq_of_cone hD hA hB h
  have e1 : angLT n m ↔ half n ≤ half m := angLT_iff_half_le hn hm hB
  have e2 : angLT m n' ↔ half m ≤ half n' := angLT_iff_half_le hm hn' hA
  have e3 : angLT n n' ↔ half n ≤ half n' := angLT_iff_half_le hn hn' hD
  have e4 : angLT n' n ↔ half n' < half n := by
    refine angLT_iff_half_lt hn' hn ?_
    have h : det n' n = -det n n' := by simp only [det]; ring
    omega
  unfold CycBtw
  rcases half_cases n with p0 | p1 <;> rcases half_cases m with q0 | q1 <;>
      rcases half_cases n' with r0 | r1
  · exact Or.inl ⟨e3.mpr (by omega), e1.mpr (by omega), e2.mpr (by omega)⟩
  · exact Or.inl ⟨e3.mpr (by omega), e1.mpr (by omega), e2.mpr (by omega)⟩
  · exact absurd (hL2 (by omega)) (by omega)
  · exact Or.inl ⟨e3.mpr (by omega), e1.mpr (by omega), e2.mpr (by omega)⟩
  · exact Or.inr ⟨e4.mpr (by omega), Or.inr (e2.mpr (by omega))⟩
  · exact absurd (hL2 (by omega)) (by omega)
  · exact Or.inr ⟨e4.mpr (by omega), Or.inl (e1.mpr (by omega))⟩
  · exact Or.inl ⟨e3.mpr (by omega), e1.mpr (by omega), e2.mpr (by omega)⟩

/-- **Gap 2, closed.**  For a set with two semi-infinite edges `n`, `n'` in
non-(anti)parallel directions ordered so that `0 < det n n'`, the whole edge set is a
cyclic-order interval from `n` to `n'`: this is exactly Colle's `w ≺ ⋯ ≺ w'`
(Definition 3.1), which `LatticeEdges.lean` could only assume (field
`IsRegion.precedes`). -/
theorem precedesAll_of_two_semiInf {R : Set (ℤ × ℤ)} {n n' : ℤ × ℤ}
    (hn : IsSemiInfEdge R n) (hn' : IsSemiInfEdge R n') (hD : 0 < det n n') :
    PrecedesAll R n n' := by
  obtain ⟨hnE, hinf⟩ := hn
  obtain ⟨hn'E, hinf'⟩ := hn'
  refine ⟨hnE, hn'E, ((ne_of_det_pos hD).1).symm, fun k hk h1 h2 => ?_⟩
  obtain ⟨x, hx, -, -, -⟩ := hk.2
  obtain ⟨hB, hA⟩ := det_nonneg_of_semiInf hD hinf hinf' ⟨x, hx⟩
  have hA0 : det k n' ≠ 0 := fun h => h2 (eq_right_of_det_eq_zero hD hk.1 hn'E.1 hB h)
  have hB0 : det n k ≠ 0 := fun h => h1 (eq_left_of_det_eq_zero hD hnE.1 hk.1 hA h)
  exact cycBtw_of_cone hnE.1.ne_zero hk.1.ne_zero hn'E.1.ne_zero
    (lt_of_le_of_ne hB (Ne.symm hB0)) (lt_of_le_of_ne hA (Ne.symm hA0)) hD

/-! ## §6. `IsRegion` without the two derived fields -/

/-- **Colle, Definition 3.1, as a constructor.**  To exhibit an `(ℓ,ℓ')`-region one
only has to produce: lattice convexity, the two semi-infinite edges in the right
cyclic order (`0 < det n n'`), and the fact that there are no further semi-infinite
edges.  Positive area, finiteness of the edge set and `w ≺ ⋯ ≺ w'` are **theorems**
(`posArea_of_edges`, `finite_E_of_two_semiInf`, `precedesAll_of_two_semiInf`). -/
theorem isRegion_of_two_semiInf {R : Set (ℤ × ℤ)} {n n' : ℤ × ℤ}
    (hlc : IsLatticeConvexRegion R) (hn : IsSemiInfEdge R n) (hn' : IsSemiInfEdge R n')
    (hD : 0 < det n n') (huniq : ∀ k, IsSemiInfEdge R k → k = n ∨ k = n') :
    IsRegion R n n' where
  latticeConvex := hlc
  infinite := hn.2.mono (face_subset R n)
  posArea := posArea_of_edges hn.1 hn'.1 (ne_of_det_pos hD).1 (ne_of_det_pos hD).2
  edgesFinite := finite_E_of_two_semiInf hn hn' hD
  semiInf := hn
  semiInf' := hn'
  detPos := hD
  semiInfUnique := huniq
  precedes := precedesAll_of_two_semiInf hn hn' hD

/-- Non-vacuity: the quarter plane, an honestly infinite region with an infinite edge
set *a priori*, satisfies the hypotheses of `finite_E_of_two_semiInf` and
`precedesAll_of_two_semiInf`, and both conclusions come out right. -/
theorem finite_E_quad' : (E quad).Finite :=
  finite_E_of_two_semiInf ⟨by rw [E_quad]; simp, infinite_face_quad_left⟩
    ⟨by rw [E_quad]; simp, infinite_face_quad_bot⟩ (by decide)

theorem precedesAll_quad' : PrecedesAll quad (-1, 0) (0, -1) :=
  precedesAll_of_two_semiInf ⟨by rw [E_quad]; simp, infinite_face_quad_left⟩
    ⟨by rw [E_quad]; simp, infinite_face_quad_bot⟩ (by decide)

/-- Non-vacuity for the constructor: it rebuilds `isRegion_quad` from strictly fewer
inputs (no `posArea`, no `edgesFinite`, no `precedes`). -/
theorem isRegion_quad' : IsRegion quad (-1, 0) (0, -1) :=
  isRegion_of_two_semiInf isLatticeConvexRegion_quad
    ⟨by rw [E_quad]; simp, infinite_face_quad_left⟩
    ⟨by rw [E_quad]; simp, infinite_face_quad_bot⟩ (by decide)
    (fun k hk => by
      have := hk.1
      rw [E_quad] at this
      simpa using this)

/-! ## §7. Intersecting with a half-plane

Colle's Claim 3.7 and Lemma 4.1 cut a region by a half-plane `ℋ(ℓ) = {z : ⟨k,z⟩ ≤ b}`.
What is **true** and what is **false** here is delicate, so both are recorded.

* `face_inter_of_subset` / `mem_E_inter_of_subset`: an edge whose face already lies
  inside the half-plane survives untouched, with the *same* face and hence the same
  cardinality.
* `face_inter_slice`: the cut direction `k` acquires the full slice `{z ∈ R : ⟨k,z⟩ = b}`
  as its face.
* `isLatticeConvexRegion_inter_halfPlaneLE`: lattice convexity is preserved.
* `not_E_inter_subset`: **`E(R ∩ ℋ) ⊆ E(R) ∪ {k}` is false.**  Cutting can create edge
  directions that are neither old edges nor the cut normal, so `Enveloped` is *not*
  preserved by half-plane intersection in general. -/

/-- **An edge whose face already lies inside the half-plane is untouched by the cut.**
The nonemptiness hypothesis cannot be dropped: for `R = quad`, `m = (1,0)` one has
`face R m = ∅ ⊆ H` for `H = {z : z₁ ≤ 0}`, yet `face (R ∩ H) (1,0) = {0} × ℕ ≠ ∅`. -/
theorem face_inter_of_subset {R H : Set (ℤ × ℤ)} {m : ℤ × ℤ} (hne : (face R m).Nonempty)
    (hsub : face R m ⊆ H) : face (R ∩ H) m = face R m := by
  obtain ⟨a, ha⟩ := hne
  ext z
  constructor
  · rintro ⟨⟨hzR, hzH⟩, hmax⟩
    have h1 : dot m a ≤ dot m z := hmax a ⟨ha.1, hsub ha⟩
    have h2 : dot m z ≤ dot m a := ha.2 z hzR
    exact ⟨hzR, fun y hy => by have := ha.2 y hy; omega⟩
  · intro hz
    exact ⟨⟨hz.1, hsub hz⟩, fun y hy => hz.2 y hy.1⟩

/-- Same, packaged for edges: the direction stays an edge and the face is literally the
same set, so its cardinality is unchanged. -/
theorem mem_E_inter_of_subset {R H : Set (ℤ × ℤ)} {m : ℤ × ℤ} (hm : m ∈ E R)
    (hsub : face R m ⊆ H) : m ∈ E (R ∩ H) ∧ face (R ∩ H) m = face R m := by
  have hne : (face R m).Nonempty := hm.2.nonempty
  exact ⟨⟨hm.1, (face_inter_of_subset hne hsub) ▸ hm.2⟩, face_inter_of_subset hne hsub⟩

/-- **The face in the cut direction is the whole slice**, provided the cutting line
actually meets `R` in a lattice point.  That hypothesis is necessary: for
`R = {(2t, 0) : t ∈ ℤ}`, `k = (1,0)`, `b = 1` the maximum of `dot k` on `R ∩ ℋ` is `0`,
not `b`. -/
theorem face_inter_slice {R : Set (ℤ × ℤ)} {k z₀ : ℤ × ℤ} {b : ℤ} (hz₀ : z₀ ∈ R)
    (hb : dot k z₀ = b) :
    face (R ∩ halfPlaneLE k b) k = {z | z ∈ R ∧ dot k z = b} := by
  have hmem : z₀ ∈ R ∩ halfPlaneLE k b := ⟨hz₀, by
    simp only [halfPlaneLE, Set.mem_ofPred_eq]; omega⟩
  ext z
  constructor
  · rintro ⟨⟨hzR, hzH⟩, hmax⟩
    simp only [halfPlaneLE, Set.mem_ofPred_eq] at hzH
    have := hmax z₀ hmem
    exact ⟨hzR, by omega⟩
  · rintro ⟨hzR, hzb⟩
    refine ⟨⟨hzR, by simp only [halfPlaneLE, Set.mem_ofPred_eq]; omega⟩, ?_⟩
    rintro y ⟨-, hyH⟩
    simp only [halfPlaneLE, Set.mem_ofPred_eq] at hyH
    omega

theorem halfPlaneLE_eq_preimage (k : ℤ × ℤ) (b : ℤ) :
    halfPlaneLE k b = toReal ⁻¹' {p : ℝ × ℝ | (k.1 : ℝ) * p.1 + (k.2 : ℝ) * p.2 ≤ (b : ℝ)} := by
  ext z
  simp only [halfPlaneLE, Set.mem_ofPred_eq, Set.mem_preimage, toReal, dot]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

/-- **Lattice convexity is preserved by intersecting with a rational half-plane.** -/
theorem isLatticeConvexRegion_inter_halfPlaneLE {R : Set (ℤ × ℤ)} (k : ℤ × ℤ) (b : ℤ)
    (hR : IsLatticeConvexRegion R) : IsLatticeConvexRegion (R ∩ halfPlaneLE k b) := by
  obtain ⟨C, hconv, hclosed, hRC⟩ := hR
  refine ⟨C ∩ {p : ℝ × ℝ | (k.1 : ℝ) * p.1 + (k.2 : ℝ) * p.2 ≤ (b : ℝ)}, ?_, ?_, ?_⟩
  · refine hconv.inter ?_
    have : {p : ℝ × ℝ | (k.1 : ℝ) * p.1 + (k.2 : ℝ) * p.2 ≤ (b : ℝ)}
        = {p : ℝ × ℝ | (fun q : ℝ × ℝ => (k.1 : ℝ) * q.1 + (k.2 : ℝ) * q.2) p ≤ (b : ℝ)} := rfl
    rw [this]
    refine convex_halfSpace_le ⟨fun u v => ?_, fun c u => ?_⟩ _
    · simp only [Prod.fst_add, Prod.snd_add]; ring
    · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  · refine hclosed.inter (isClosed_le ?_ continuous_const)
    exact (continuous_const.mul continuous_fst).add (continuous_const.mul continuous_snd)
  · rw [Set.preimage_inter, ← hRC, ← halfPlaneLE_eq_preimage]

/-! ### §8. The counterexample: `E(R ∩ ℋ) ⊈ E(R) ∪ {k}`

**Gap 3 cannot be closed as stated.** Cutting a region by a half-plane can create edge
directions that are *neither* old edges *nor* the cut normal.  Here is a verified
witness.

Take `R = box (0,0) (3,3)`, so `E(R) = {(±1,0), (0,±1)}` (the four axis directions).
Cut by `k = (1,2)`, `b = 8`.  The point `(3,3)` has `dot k (3,3) = 9 > 8`, so it is
removed.  The points `(2,3)` and `(3,2)` both survive the cut: `dot k (2,3) = 8`
exactly (on the cutting line) and `dot k (3,2) = 7 < 8` (strictly inside).  Now
consider `m = (1,1)`:

* On the full box `R`, the maximum of `dot m · = z₁ + z₂` is `6`, attained uniquely at
  `(3,3)`, so `face R m = {(3,3)}` is a singleton and `m ∉ E(R)`.
* On `R ∩ ℋ`, the maximum of `z₁ + z₂` is `5`, attained at both `(2,3)` and `(3,2)`,
  so `face (R ∩ ℋ) m = {(2,3), (3,2)}` is nontrivial (and `gcd(1,1) = 1`), hence
  `m ∈ E(R ∩ ℋ)`.

Thus `m ∈ E(R ∩ ℋ) ∖ (E(R) ∪ {k})`, and the naive inclusion fails. -/

theorem box_face_1_1 : face (box (0, 0) (3, 3)) (1, 1) = {(3, 3)} := by
  ext z
  simp only [mem_face_iff, mem_box, Set.mem_singleton_iff, dot]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, hmax⟩
    have h6 := hmax (3, 3) ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
    simp only at h6
    have hz : z.1 = 3 ∧ z.2 = 3 := by omega
    exact Prod.ext_iff.mpr ⟨hz.1, hz.2⟩
  · rintro rfl
    refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_⟩
    rintro y ⟨a, b, c, d⟩
    omega

theorem not_mem_E_box_1_1 : (1, 1) ∉ E (box (0, 0) (3, 3)) := by
  intro h
  have := h.2
  rw [box_face_1_1] at this
  exact Set.not_nontrivial_singleton this

theorem face_box_inter_1_1 :
    face (box (0, 0) (3, 3) ∩ halfPlaneLE (1, 2) 8) (1, 1) = {(2, 3), (3, 2)} := by
  ext z
  simp only [mem_face_iff, Set.mem_inter_iff, mem_box, halfPlaneLE, Set.mem_ofPred_eq, dot]
  constructor
  · rintro ⟨⟨⟨h1, h2, h3, h4⟩, h5⟩, hmax⟩
    have e1 := hmax (2, 3) ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
    simp only at e1
    have hz : (z.1 = 2 ∧ z.2 = 3) ∨ (z.1 = 3 ∧ z.2 = 2) := by omega
    rcases hz with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl (Prod.ext_iff.mpr ⟨ha, hb⟩)
    · exact Or.inr (Prod.ext_iff.mpr ⟨ha, hb⟩)
  · rintro (rfl | rfl)
    · refine ⟨⟨⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩, ?_⟩
      rintro y ⟨⟨a, b, c, d⟩, e⟩
      omega
    · refine ⟨⟨⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩, ?_⟩
      rintro y ⟨⟨a, b, c, d⟩, e⟩
      omega

theorem mem_E_box_inter_1_1 : (1, 1) ∈ E (box (0, 0) (3, 3) ∩ halfPlaneLE (1, 2) 8) := by
  refine ⟨by decide, ?_⟩
  rw [face_box_inter_1_1]
  refine ⟨(2, 3), by simp, (3, 2), by simp, by decide⟩

/-- **Gap 3, honest negative result.**  The naive hope
`E(R ∩ ℋ(k, b)) ⊆ E(R) ∪ {k}` is **false**: cutting can create edge directions that
are neither old edges nor the cut normal.  This theorem records a verified
counterexample. -/
theorem not_E_inter_subset :
    ¬ ∀ (R : Set (ℤ × ℤ)) (k : ℤ × ℤ) (b : ℤ),
      E (R ∩ halfPlaneLE k b) ⊆ E R ∪ {k} := by
  intro h
  specialize h (box (0, 0) (3, 3)) (1, 2) 8
  have : (1, 1) ∈ E (box (0, 0) (3, 3)) ∪ {(1, 2)} := h mem_E_box_inter_1_1
  simp only [Set.mem_union, Set.mem_singleton_iff] at this
  rcases this with h1 | h2
  · exact not_mem_E_box_1_1 h1
  · norm_num at h2

/-! ## Status

Score against the three gaps left open by `LatticeEdges.lean`.

**Gap 1 — `|E(ℛ)| < ∞` (Colle Def. 3.1): CLOSED.**
`finite_E_of_two_semiInf`.  Two semi-infinite edges with `0 < det n n'` force
finiteness of `E R`; no convexity, closedness or boundedness hypothesis is used.

**Gap 2 — `w ≺ ⋯ ≺ w'` (Colle Def. 3.1): CLOSED.**
`precedesAll_of_two_semiInf`, via `cycBtw_of_cone` and the order/determinant
dictionary `angLT_iff_det`.  Same hypotheses as Gap 1.

Consequently `isRegion_of_two_semiInf` builds `IsRegion R n n'` without the fields
`posArea`, `edgesFinite`, `precedes`, and `isRegion_quad'` / `finite_E_quad'` /
`precedesAll_quad'` witness that the hypotheses are satisfiable (non-vacuity).

**Gap 3 — behaviour of `E(·)` under `· ∩ ℋ(ℓ)` (Colle Claim 3.7, Lemma 4.1):
the naive form is REFUTED; the form the downstream actually needs is CLOSED,
in `RegionCutLeftEdge.lean` and `RegionHalfPlaneOrientation.lean`.**

What is proved positively:
* `face_inter_of_subset`, `mem_E_inter_of_subset` — an edge whose face already lies
  in the half-plane survives with the *same* face (so same cardinality);
* `face_inter_slice` — the cut normal `k` acquires the whole slice as its face,
  provided the cutting line meets `R` in a lattice point (hypothesis necessary);
* `isLatticeConvexRegion_inter_halfPlaneLE` — lattice convexity is preserved.

What is false: `not_E_inter_subset` refutes `E(R ∩ ℋ(k,b)) ⊆ E(R) ∪ {k}` by the
verified §8 witness.  Hence `Enveloped` is **not** preserved by half-plane
intersection in general, and a downstream use of Claim 3.7 / Lemma 4.1 must say
*which* half-plane it cuts with.  That extra condition is now identified and both
directions are settled by the kernel:

* `RegionCutLeftEdge.isSemiInfEdge_inter_halfPlaneLE_left` — cutting an
  `IsRegion R n n'` with `halfPlaneLE n' c` keeps `n` a semi-infinite edge, for
  every `c`.  Its engine is `infinite_face_inter_halfPlaneLE`; the §8 witness is
  `isSemiInfEdge_quad_cut_left`.
* `RegionHalfPlaneOrientation.not_isRegion_inter_halfPlaneGE` — the opposite
  orientation fails: `quad ∩ halfPlaneGE (0,-1) (-1)` is bounded in the `n`
  direction, so `n` stops being semi-infinite (`not_isSemiInfEdge_quadGE_left`).
  `isRegion_quad_inter_halfPlaneLE` witnesses that `halfPlaneLE` does work.

So the orientation is not a convention: `halfPlaneLE n' c` is forced.

Axiom hygiene — generated, not hand-written.  `tmp/regionedges_axioms.lean`
`#print axioms` on all 40 declarations of this file; run via
`bash scripts/check1.sh` (which pins the `lakefile.toml` `[leanOptions]`, see
`blueprint/NOTE.md` "验证口径漏洞").  Result: no `axiom` command in this file, no
`sorry` (`check1.sh Nivat/External/Colle/RegionEdges.lean` → `EXIT=0`, no
`declaration uses 'sorry'`), and every declaration's closure is contained in
`[propext, Classical.choice, Quot.sound]` — four of them use strictly less
(`half_cases` depends on no axioms; `half_eq_zero_iff`, `half_eq_one_iff` on
`propext` alone; the `cramer_*` and `face_inter_*` group on `[propext, Quot.sound]`).
-/

end Nivat.LE2
