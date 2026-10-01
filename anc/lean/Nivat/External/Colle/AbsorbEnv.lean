/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges

/-!
Landed from `tmp/absorb_3bprime.lean` (2026-09-18, compiled clean, zero consumers until
`ChainAssemble.lean`'s item-(ii) recursion) as `Nivat/External/Colle/AbsorbEnv.lean`,
lane Aenvfix, 2026-09-19, by team-lead's ruling.  Content unchanged except this note and the
`3b′` label, which was a `tmp/` naming habit.
-/

/-!
# Absorbing enlargement (Collé item (ii) engine) — an `E(𝒰)`-enveloped set absorbing any prescribed finite set, at a fixed support level

**What this file proves** (`Nivat.Absorb.exists_enveloped_absorbing`): given an
`E(𝒰)`-enveloped `B`, an edge normal `n ∈ E(𝒰)`, and *any* finite `F` lying in the closed
half plane `{z | ⟪n,z⟫ ≤ suppVal B n}` that supports `B` along `n`, there is an
`E(𝒰)`-enveloped `B₁ ⊇ B ∪ F` with the **same** `n`-support level.

This is the absorbing form team-lead asked for, and it is what Collé's item (ii)
(`b3_colle2.txt:476`) needs: `B_i ⊇ [-i+1,i-1]² ∩ ℋ(ℓ^(−))` is exactly "absorb a prescribed
box inside the half plane".  The sentence Collé skips is at `:462` — *"The assumption on
item (i) allows us to construct a sequence"* — where the antecedent as written only gives
"there exists a larger `B`".  Plain enlargement is discharged by the identity witness
`B := B'` and therefore has no content; **absorption of a prescribed finite set is the
statement with content**, and `B ⊊ B₁` comes out of it for free whenever `F ⊄ B`.

## The construction

Two homotheties, packaged as one.  Let `a ≠ b` be two lattice points of the edge
`face B n` (they exist because `n ∈ E B`, `E B = E U`).  With

* `K` a large positive integer,
* `w := K • a + (K-1) • b`,
* `dil B (2K) := {z | ∀ m, ⟪m,z⟫ ≤ 2K · suppVal B m}` the `2K`-fold dilation,

put `B₁ := shift (-w) (dil B (2K))`, i.e. `z ∈ B₁ ↔ z + w ∈ dil B (2K)`.  On support values
this is `suppVal B₁ m = 2K·suppVal B m − K·⟪m,a⟫ − (K−1)·⟪m,b⟫`, i.e. the homothety of ratio
`2K` about the **midpoint** of `a` and `b` — a point in the *relative interior* of the edge,
which is why the union over `K` is the whole half plane and not merely a tangent cone.  The
midpoint itself is generally not a lattice point; writing the construction through support
values rather than through a centre avoids that entirely.

The single arithmetic fact that carries the whole proof is

    for every `m ∈ E B` other than `n`,  `2·suppVal B m − ⟪m,a⟫ − ⟪m,b⟫ ≥ 1`

(`Nivat.Absorb.one_le_slack`): `a` and `b` cannot both lie on the `m`-face, since they are
distinct points of the `n`-face and two distinct primitive normals cannot expose a common
segment.  The excluded case `m = -n` is where `PosArea B` is consumed.

## Conventions, flagged because this tree runs both

* **Sign.**  `face R n` (`LatticeEdges.lean:160`) is the `⟪n,·⟫`-**maximising** face, so `n`
  is an *outer* normal and the half plane containing `B` is `{z | ⟪n,z⟫ ≤ suppVal B n}`.
  `ChainGeom.lean:32` runs the other convention (*"the `-n_J` in `lex`/`lex'` is because the
  face is minimal, not maximal"*); a consumer working with a minimal face must pass `-n`.
* **`B.Finite` is a hypothesis, not a derivation.**  Per team-lead: `Enveloped.finite`
  (`MaximalEnveloped.lean:157`) needs two independent antipodal pairs in `E U`, which
  `exists_two_nonparallel_edge_normals` (`EdgeNormals.lean:38`) supplies for `𝒮_φ`; that is
  a different lane's job.  Taken as an input here.
* **`PosArea B` is a hypothesis, not smuggled in.**  Lean's `Enveloped`
  (`LatticeEdges.lean:628`) does *not* carry Def 3.2's positive-area clause.  It is an
  explicit argument; `exists_enveloped_absorbing_of_three_edges` below derives it from three
  distinct edges of `U` via `posArea_of_envOf` (`LatticeEdges.lean:2451`) for callers that
  have them.
* **Def 3.2 *parallel* vs same-normal is dodged, not decided.**  The construction gives
  `E B₁ = E B` on the nose (`E_dil` + `E_shift`), so it is insensitive to whether Collé's
  "parallel" is read as `E(𝒯) = E(𝒰)` or `E(𝒯) ⊆ ±E(𝒰)`.  Nothing below uses orientation.
-/

namespace Nivat.Absorb

open Nivat Nivat.LE2

/-! ## 1. A lattice normal as a linear functional on `ℝ²` -/

/-- `⟪m, ·⟫ : ℝ² → ℝ` for a lattice normal `m`, as a bundled linear map (we need `map_sum`
and `map_smul` for the convex-combination argument of `mem_convexHull_of_eq_max`). -/
def lin (m : ℤ × ℤ) : (ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun x := (m.1 : ℝ) * x.1 + (m.2 : ℝ) * x.2
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add]; ring
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem lin_apply (m : ℤ × ℤ) (x : ℝ × ℝ) :
    lin m x = (m.1 : ℝ) * x.1 + (m.2 : ℝ) * x.2 := rfl

theorem lin_toReal (m z : ℤ × ℤ) : lin m (toReal z) = ((dot m z : ℤ) : ℝ) := by
  rw [lin_apply, dot_cast_toReal]

theorem lin_smul_toReal (m z : ℤ × ℤ) (r : ℝ) :
    lin m (r • toReal z) = r * ((dot m z : ℤ) : ℝ) := by
  rw [lin_apply]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [← dot_cast_toReal]
  ring

/-! ## 2. The face of a convex hull is the hull of the face

For a convex combination attaining the maximum of a linear functional, every point of the
combination with positive weight already attains the maximum.  This is the one genuinely
real-analytic ingredient; everything else below is arithmetic in `ℤ`. -/

theorem mem_convexHull_of_eq_max {s : Set (ℝ × ℝ)} {m : ℤ × ℤ} {M : ℝ}
    (hs : ∀ y ∈ s, lin m y ≤ M) {x : ℝ × ℝ}
    (hx : x ∈ convexHull ℝ s) (hxM : lin m x = M) :
    x ∈ convexHull ℝ {y | y ∈ s ∧ lin m y = M} := by
  classical
  rw [convexHull_eq] at hx
  obtain ⟨ι, t, w, zz, hw₀, hw₁, hzs, hcm⟩ := hx
  have hcm' : t.centerMass w zz = ∑ i ∈ t, w i • zz i :=
    Finset.centerMass_eq_of_sum_1 _ _ hw₁
  have hlx : lin m x = ∑ i ∈ t, w i * lin m (zz i) := by
    rw [← hcm, hcm', map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; simp
  have hzero : ∑ i ∈ t, w i * (M - lin m (zz i)) = 0 := by
    have e : ∀ i ∈ t, w i * (M - lin m (zz i)) = w i * M - w i * lin m (zz i) :=
      fun i _ => by ring
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.sum_mul, hw₁, one_mul,
      ← hlx, hxM]
    ring
  have hterm : ∀ i ∈ t, w i * (M - lin m (zz i)) = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hzero
    intro i hi
    exact mul_nonneg (hw₀ i hi) (by linarith [hs _ (hzs i hi)])
  set t' := t.filter (fun i => lin m (zz i) = M) with ht'
  have hsub : t' ⊆ t := Finset.filter_subset _ _
  have hwz : ∀ i ∈ t, i ∉ t' → w i = 0 := by
    intro i hi hni
    have hne : lin m (zz i) ≠ M := fun h => hni (Finset.mem_filter.mpr ⟨hi, h⟩)
    rcases mul_eq_zero.mp (hterm i hi) with h | h
    · exact h
    · exact absurd (by linarith : lin m (zz i) = M) hne
  have hw₁' : ∑ i ∈ t', w i = 1 := by
    rw [Finset.sum_subset hsub fun i hi hni => hwz i hi hni]; exact hw₁
  have hcm'' : t'.centerMass w zz = x := by
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw₁', ← hcm, hcm']
    exact Finset.sum_subset hsub fun i hi hni => by rw [hwz i hi hni, zero_smul]
  rw [← hcm'']
  exact Finset.centerMass_mem_convexHull t' (fun i hi => hw₀ i (hsub hi))
    (by rw [hw₁']; norm_num)
    (fun i hi => ⟨hzs i (hsub hi), (Finset.mem_filter.mp hi).2⟩)

/-- For a finite lattice set the closed convex hull is already the convex hull. -/
theorem convHullOf_eq_convexHull {T : Set (ℤ × ℤ)} (hfin : T.Finite) :
    convHullOf T = convexHull ℝ (toReal '' T) :=
  ((hfin.image toReal).isClosed_convexHull (𝕜 := ℝ)).closure_eq

/-! ## 3. Elementary algebra of dilation -/

theorem dot_smul_right (m : ℤ × ℤ) (k : ℤ) (z : ℤ × ℤ) : dot m (k • z) = k * dot m z := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem smul_injective {k : ℤ} (hk : k ≠ 0) {x y : ℤ × ℤ} (h : k • x = k • y) : x = y := by
  have h1 : k * x.1 = k * y.1 := by simpa using congrArg Prod.fst h
  have h2 : k * x.2 = k * y.2 := by simpa using congrArg Prod.snd h
  exact Prod.ext (mul_left_cancel₀ hk h1) (mul_left_cancel₀ hk h2)

/-! ## 4. The dilation `k · T`

`dil T k` is the set of lattice points of the `k`-fold dilate of `conv T`, written through
support values so that membership is an arithmetic condition. -/

/-- The lattice points of `k · conv(T)`. -/
def dil (T : Set (ℤ × ℤ)) (k : ℤ) : Set (ℤ × ℤ) :=
  {z | ∀ m : ℤ × ℤ, dot m z ≤ k * suppVal T m}

theorem mem_dil {T : Set (ℤ × ℤ)} {k : ℤ} {z : ℤ × ℤ} :
    z ∈ dil T k ↔ ∀ m : ℤ × ℤ, dot m z ≤ k * suppVal T m := Iff.rfl

/-- The scaling bridge: the `m`-inequality at level `k·c` for `z` is the `m`-inequality at
level `c` for the real point `k⁻¹ · z`. -/
theorem smul_inv_mem_realHalfPlaneLE_iff {m z : ℤ × ℤ} {k : ℤ} (hk : 0 < k) (c : ℤ) :
    ((k : ℝ)⁻¹ • toReal z) ∈ realHalfPlaneLE m c ↔ dot m z ≤ k * c := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [mem_realHalfPlaneLE, ← lin_apply, lin_smul_toReal]
  constructor
  · intro h
    have h' := mul_le_mul_of_nonneg_left h (le_of_lt hkR)
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hkR), one_mul] at h'
    exact_mod_cast h'
  · intro h
    have h' : ((dot m z : ℤ) : ℝ) ≤ (k : ℝ) * ((c : ℤ) : ℝ) := by exact_mod_cast h
    have h'' := mul_le_mul_of_nonneg_left h' (le_of_lt (inv_pos.mpr hkR))
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hkR), one_mul] at h''
    exact h''

/-- **`dil T k` is the lattice preimage of the dilated hull.**  This is the statement that
makes lattice convexity and the edge computation available. -/
theorem dil_eq_preimage {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty)
    (harea : PosArea T) {k : ℤ} (hk : 0 < k) :
    dil T k = toReal ⁻¹' ((fun x : ℝ × ℝ => (k : ℝ)⁻¹ • x) ⁻¹' convHullOf T) := by
  ext z
  simp only [Set.mem_preimage]
  constructor
  · intro hz
    exact iInter_subset_convHullOf hfin hne harea
      (Set.mem_iInter₂.mpr fun m _ => (smul_inv_mem_realHalfPlaneLE_iff hk _).mpr (hz m))
  · intro hx m
    exact (smul_inv_mem_realHalfPlaneLE_iff hk _).mp
      (convHullOf_subset_realHalfPlaneLE hfin hne m hx)

/-- Only the *edge* inequalities have to be checked. -/
theorem mem_dil_of_mem_E {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty)
    (harea : PosArea T) {k : ℤ} (hk : 0 < k) {z : ℤ × ℤ}
    (h : ∀ m ∈ E T, dot m z ≤ k * suppVal T m) : z ∈ dil T k := by
  rw [dil_eq_preimage hfin hne harea hk]
  simp only [Set.mem_preimage]
  exact iInter_subset_convHullOf hfin hne harea
    (Set.mem_iInter₂.mpr fun m hm => (smul_inv_mem_realHalfPlaneLE_iff hk _).mpr (h m hm))

theorem smul_mem_dil {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty) {k : ℤ}
    (hk : 0 ≤ k) {z : ℤ × ℤ} (hz : z ∈ T) : k • z ∈ dil T k := by
  intro m
  rw [dot_smul_right]
  exact mul_le_mul_of_nonneg_left (le_suppVal hfin hne hz) hk

theorem smul_mem_face_dil {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty) {k : ℤ}
    (hk : 0 ≤ k) {m v : ℤ × ℤ} (hv : v ∈ face T m) : k • v ∈ face (dil T k) m := by
  refine ⟨smul_mem_dil hfin hne hk hv.1, fun y hy => ?_⟩
  rw [dot_smul_right, ← suppVal_eq hv]
  exact hy m

theorem suppVal_dil {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty) {k : ℤ}
    (hk : 0 ≤ k) (m : ℤ × ℤ) : suppVal (dil T k) m = k * suppVal T m := by
  obtain ⟨v, hv⟩ := face_nonempty hfin hne m
  rw [suppVal_eq (smul_mem_face_dil hfin hne hk hv), dot_smul_right, suppVal_eq hv]

theorem dil_finite (T : Set (ℤ × ℤ)) (k : ℤ) : (dil T k).Finite := by
  have hsub : dil T k
      ⊆ (Set.Icc (-(k * suppVal T (-1, 0))) (k * suppVal T (1, 0)))
        ×ˢ (Set.Icc (-(k * suppVal T (0, -1))) (k * suppVal T (0, 1))) := by
    intro z hz
    have h1 := hz ((1 : ℤ), (0 : ℤ))
    have h2 := hz ((-1 : ℤ), (0 : ℤ))
    have h3 := hz ((0 : ℤ), (1 : ℤ))
    have h4 := hz ((0 : ℤ), (-1 : ℤ))
    simp only [dot] at h1 h2 h3 h4
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  exact ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _)).subset hsub

theorem dil_nonempty {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty) {k : ℤ}
    (hk : 0 ≤ k) : (dil T k).Nonempty := by
  obtain ⟨v, hv⟩ := hne
  exact ⟨k • v, smul_mem_dil hfin ⟨v, hv⟩ hk hv⟩

theorem dil_isLatticeConvexRegion {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty)
    (harea : PosArea T) {k : ℤ} (hk : 0 < k) : IsLatticeConvexRegion (dil T k) := by
  refine ⟨(fun x : ℝ × ℝ => (k : ℝ)⁻¹ • x) ⁻¹' convHullOf T, ?_, ?_,
    dil_eq_preimage hfin hne harea hk⟩
  · intro x hx y hy s t hs ht hst
    have e : (k : ℝ)⁻¹ • (s • x + t • y)
        = s • ((k : ℝ)⁻¹ • x) + t • ((k : ℝ)⁻¹ • y) := by
      rw [smul_add, smul_smul, smul_smul, smul_smul, smul_smul, mul_comm ((k : ℝ)⁻¹) s,
        mul_comm ((k : ℝ)⁻¹) t]
    show (k : ℝ)⁻¹ • (s • x + t • y) ∈ convHullOf T
    rw [e]
    exact convex_convHullOf T hx hy hs ht hst
  · exact IsClosed.preimage (by fun_prop) (isClosed_convHullOf T)

/-- **The dilation has exactly the edge normals of the original.**  The `⊇` half is the
injection `z ↦ k • z`; the `⊆` half is where `mem_convexHull_of_eq_max` is consumed — it is
what rules out the *spurious* edges that an arbitrary integer H-representation would
acquire (e.g. `{z | 0 ≤ z.1 ≤ 2, 0 ≤ z.2 ≤ 2, 2z.1 + z.2 ≤ 3}` has the edge `(1,1)`, which
is none of its four defining normals). -/
theorem E_dil {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty) (harea : PosArea T)
    {k : ℤ} (hk : 0 < k) : E (dil T k) = E T := by
  have hk0 : k ≠ 0 := ne_of_gt hk
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  ext m
  constructor
  · rintro ⟨hprim, hnt⟩
    refine ⟨hprim, ?_⟩
    by_contra hcon
    obtain ⟨t₀, ht₀⟩ := face_nonempty hfin hne m
    have hss : face T m = {t₀} :=
      (Set.not_nontrivial_iff.mp hcon).eq_singleton_of_mem ht₀
    -- every point of the dilated face is `k • t₀`
    have hkey : ∀ p ∈ face (dil T k) m, toReal p = (k : ℝ) • toReal t₀ := by
      intro p hp
      have hdp : dot m p = k * suppVal T m := by
        rw [← suppVal_dil hfin hne (le_of_lt hk) m, suppVal_eq hp]
      have hx : ((k : ℝ)⁻¹ • toReal p) ∈ convHullOf T := by
        have := hp.1
        rw [dil_eq_preimage hfin hne harea hk] at this
        exact this
      rw [convHullOf_eq_convexHull hfin] at hx
      have hval : lin m ((k : ℝ)⁻¹ • toReal p) = ((suppVal T m : ℤ) : ℝ) := by
        rw [lin_smul_toReal, hdp]
        push_cast
        field_simp
      have hbnd : ∀ y ∈ toReal '' T, lin m y ≤ ((suppVal T m : ℤ) : ℝ) := by
        rintro _ ⟨z, hz, rfl⟩
        rw [lin_toReal]
        exact_mod_cast le_suppVal hfin hne hz
      have hmem := mem_convexHull_of_eq_max hbnd hx hval
      have hsub : {y | y ∈ toReal '' T ∧ lin m y = ((suppVal T m : ℤ) : ℝ)}
          ⊆ {toReal t₀} := by
        rintro _ ⟨⟨z, hz, rfl⟩, hzv⟩
        have hzeq : dot m z = suppVal T m := by
          rw [lin_toReal] at hzv; exact_mod_cast hzv
        have : z ∈ face T m := by
          rw [face_eq_of_support (fun y hy => le_suppVal hfin hne hy)
            (exists_suppVal_eq hfin hne m)]
          exact ⟨hz, hzeq⟩
        rw [hss] at this
        have hz0 : z = t₀ := this
        exact Set.mem_singleton_iff.mpr (congrArg toReal hz0)
      have : ((k : ℝ)⁻¹ • toReal p) ∈ ({toReal t₀} : Set (ℝ × ℝ)) := by
        have := convexHull_mono hsub hmem
        rwa [convexHull_singleton] at this
      have he : (k : ℝ)⁻¹ • toReal p = toReal t₀ := this
      calc toReal p = (k : ℝ) • ((k : ℝ)⁻¹ • toReal p) := by
            rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hkR), one_smul]
        _ = (k : ℝ) • toReal t₀ := by rw [he]
    obtain ⟨p, hp, q, hq, hpq⟩ := hnt
    exact hpq (toReal_injective (by rw [hkey p hp, hkey q hq]))
  · rintro ⟨hprim, hnt⟩
    refine ⟨hprim, ?_⟩
    obtain ⟨p, hp, q, hq, hpq⟩ := hnt
    exact ⟨k • p, smul_mem_face_dil hfin hne (le_of_lt hk) hp,
      k • q, smul_mem_face_dil hfin hne (le_of_lt hk) hq,
      fun h => hpq (smul_injective hk0 h)⟩

theorem face_encard_le_dil {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hne : T.Nonempty) {k : ℤ}
    (hk : 0 < k) (m : ℤ × ℤ) : (face T m).encard ≤ (face (dil T k) m).encard :=
  Set.encard_le_encard_of_injOn
    (fun _ hz => smul_mem_face_dil hfin hne (le_of_lt hk) hz)
    (fun _ _ _ _ h => smul_injective (ne_of_gt hk) h)

/-! ## 5. Support values under translation -/

theorem suppVal_shift {X : Set (ℤ × ℤ)} (hfin : X.Finite) (hne : X.Nonempty) (v m : ℤ × ℤ) :
    suppVal (shift v X) m = suppVal X m + dot m v := by
  obtain ⟨y, hy⟩ := face_nonempty hfin hne m
  have hmem : y + v ∈ face (shift v X) m := by
    rw [face_shift]
    show (y + v) - v ∈ face X m
    simpa using hy
  rw [suppVal_eq hmem, dot_add, suppVal_eq hy]

/-! ## 6. The slack of the non-`n` edges -/

/-- **The one geometric fact.**  Two distinct lattice points of the `n`-edge cannot both sit
on another edge, so every other edge has strictly positive slack at their "midpoint"; being
integers, the slack is at least `1`.

`PosArea B` is consumed in exactly one place: the case `m = -n`, where `a` would have to
maximise *and* minimise `⟪n,·⟫`, forcing `B` onto a line. -/
theorem one_le_slack {B : Set (ℤ × ℤ)} (hfin : B.Finite) (hne : B.Nonempty)
    (harea : PosArea B) {n a b : ℤ × ℤ} (hnB : n ∈ E B)
    (ha : a ∈ face B n) (hb : b ∈ face B n) (hab : a ≠ b)
    {m : ℤ × ℤ} (hm : m ∈ E B) (hmn : m ≠ n) :
    1 ≤ 2 * suppVal B m - dot m a - dot m b := by
  have h1 : dot m a ≤ suppVal B m := le_suppVal hfin hne ha.1
  have h2 : dot m b ≤ suppVal B m := le_suppVal hfin hne hb.1
  by_contra hcon
  have hcon' : 2 * suppVal B m - dot m a - dot m b < 1 := not_le.mp hcon
  have e1 : dot m a = suppVal B m := by omega
  have e2 : dot m b = suppVal B m := by omega
  have hd0 : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hdm : dot (b - a) m = 0 := by
    rw [dot_comm, dot_sub]; omega
  have hdn : dot (b - a) n = 0 := by
    rw [dot_comm, dot_sub, dot_eq_of_mem_face hb ha]; ring
  have hdet : det m n = 0 := det_eq_zero_of_dot_eq_zero hd0 hdm hdn
  rcases eq_or_neg_of_prim_of_det_eq_zero (mem_E_iff.mp hm).1 (mem_E_iff.mp hnB).1 hdet
    with h | h
  · exact hmn h.symm
  · -- `n = -m`, i.e. `a` both maximises and minimises `⟪n,·⟫` on `B`
    have hmnn : m = -n := by rw [h]; simp
    have hconst : ∀ y ∈ B, ∀ z ∈ B, dot n y = dot n z := by
      have hmax : ∀ y ∈ B, dot n y ≤ dot n a := fun y hy => ha.2 y hy
      have hmin : ∀ y ∈ B, dot n a ≤ dot n y := by
        intro y hy
        have := le_suppVal hfin hne (n := m) hy
        rw [← e1] at this
        rw [hmnn] at this
        simp only [dot_neg_left] at this
        omega
      intro y hy z hz
      have := hmax y hy; have := hmin y hy
      have := hmax z hz; have := hmin z hz
      omega
    exact absurd harea (not_posArea_of_dot_const (mem_E_iff.mp hnB).1.ne_zero hconst)

/-! ## 7. The theorem -/

/-- **The absorbing enlargement.**  An `E(𝒰)`-enveloped `B` can be enlarged to an `E(𝒰)`-enveloped `B₁` absorbing
any prescribed finite subset `F` of the closed half plane `{⟪n,·⟫ ≤ suppVal B n}` supporting
`B` along the edge `n`, **without moving the `n`-support line**.

Strict enlargement is a corollary, not a hypothesis: whenever `F ⊄ B` one gets `B ⊊ B₁`. -/
theorem exists_enveloped_absorbing {U B : Set (ℤ × ℤ)} {n : ℤ × ℤ}
    (hEU : (E U).Finite) (hEnv : EnvOf U B) (hfin : B.Finite) (hne : B.Nonempty)
    (harea : PosArea B) (hn : n ∈ E U) (F : Finset (ℤ × ℤ))
    (hF : ∀ f ∈ F, dot n f ≤ suppVal B n) :
    ∃ B₁ : Set (ℤ × ℤ), EnvOf U B₁ ∧ B ⊆ B₁ ∧ (↑F : Set (ℤ × ℤ)) ⊆ B₁ ∧
      suppVal B₁ n = suppVal B n := by
  classical
  have hEB : E B = E U := Enveloped.E_eq hEU hEnv
  have hEBfin : (E B).Finite := by rw [hEB]; exact hEU
  have hnB : n ∈ E B := by rw [hEB]; exact hn
  obtain ⟨a, ha, b, hb, hab⟩ := (mem_E_iff.mp hnB).2
  -- the enlargement parameter
  set s : ℕ := (hEBfin.toFinset ×ˢ F).sup
    (fun pr => (dot pr.1 pr.2 - dot pr.1 b).toNat) with hs
  set K : ℤ := 1 + (s : ℤ) with hKdef
  have hK1 : 1 ≤ K := by
    have : (0 : ℤ) ≤ (s : ℤ) := Int.natCast_nonneg s
    omega
  have hK0 : (0 : ℤ) < 2 * K := by omega
  have hKbnd : ∀ m ∈ E B, ∀ f ∈ F, dot m f - dot m b ≤ K := by
    intro m hm f hf
    have hmem : (m, f) ∈ hEBfin.toFinset ×ˢ F :=
      Finset.mem_product.mpr ⟨hEBfin.mem_toFinset.mpr hm, hf⟩
    have hle : (dot m f - dot m b).toNat ≤ s := Finset.le_sup (f := fun pr =>
      (dot pr.1 pr.2 - dot pr.1 b).toNat) hmem
    have : dot m f - dot m b ≤ ((dot m f - dot m b).toNat : ℤ) := Int.self_le_toNat _
    have h2 : ((dot m f - dot m b).toNat : ℤ) ≤ (s : ℤ) := by exact_mod_cast hle
    omega
  -- the construction
  set w : ℤ × ℤ := K • a + (K - 1) • b with hw
  set D : Set (ℤ × ℤ) := dil B (2 * K) with hD
  refine ⟨shift (-w) D, ?_, ?_, ?_, ?_⟩
  · -- `EnvOf U (shift (-w) D)`
    refine envOf_of_E_eq
      (isLatticeConvexRegion_shift _ (dil_isLatticeConvexRegion hfin hne harea hK0)) ?_ ?_
    · rw [E_shift, hD, E_dil hfin hne harea hK0, hEB]
    · intro m hm
      have h1 : (face U m).encard ≤ (face B m).encard :=
        Enveloped.face_encard_le hEU hEnv hm
      have h2 : (face B m).encard ≤ (face D m).encard :=
        face_encard_le_dil hfin hne hK0 m
      have h3 : (face (shift (-w) D) m).encard = (face D m).encard := by
        rw [face_shift, encard_shift]
      rw [h3]
      exact le_trans h1 h2
  · -- `B ⊆ shift (-w) D`
    intro z hz
    show z - -w ∈ D
    have hzw : z - -w = z + w := by abel
    rw [hzw, hD]
    intro m
    have hz' : dot m z ≤ suppVal B m := le_suppVal hfin hne hz
    have ha' : dot m a ≤ suppVal B m := le_suppVal hfin hne ha.1
    have hb' : dot m b ≤ suppVal B m := le_suppVal hfin hne hb.1
    have hdw : dot m (z + w) = dot m z + K * dot m a + (K - 1) * dot m b := by
      rw [hw, dot_add, dot_add, dot_smul_right, dot_smul_right]; ring
    rw [hdw]
    have t1 : K * dot m a ≤ K * suppVal B m :=
      mul_le_mul_of_nonneg_left ha' (by omega)
    have t2 : (K - 1) * dot m b ≤ (K - 1) * suppVal B m :=
      mul_le_mul_of_nonneg_left hb' (by omega)
    have e : 2 * K * suppVal B m
        = suppVal B m + K * suppVal B m + (K - 1) * suppVal B m := by ring
    rw [e]
    linarith
  · -- `F ⊆ shift (-w) D`
    intro f hf
    have hfF : f ∈ F := by simpa using hf
    show f - -w ∈ D
    have hzw : f - -w = f + w := by abel
    rw [hzw, hD]
    refine mem_dil_of_mem_E hfin hne harea hK0 ?_
    intro m hm
    have hdw : dot m (f + w) = dot m f + K * dot m a + (K - 1) * dot m b := by
      rw [hw, dot_add, dot_add, dot_smul_right, dot_smul_right]; ring
    rw [hdw]
    by_cases hmn : m = n
    · subst hmn
      have hna : dot m a = suppVal B m := (suppVal_eq ha).symm
      have hnb : dot m b = suppVal B m := (suppVal_eq hb).symm
      have hff : dot m f ≤ suppVal B m := hF f hfF
      have e : 2 * K * suppVal B m
          = suppVal B m + K * suppVal B m + (K - 1) * suppVal B m := by ring
      rw [e, hna, hnb]
      linarith
    · have hslack : 1 ≤ 2 * suppVal B m - dot m a - dot m b :=
        one_le_slack hfin hne harea hnB ha hb hab hm hmn
      have hfb : dot m f - dot m b ≤ K := hKbnd m hm f hfF
      have hKs : K * 1 ≤ K * (2 * suppVal B m - dot m a - dot m b) :=
        mul_le_mul_of_nonneg_left hslack (by omega)
      nlinarith [hKs, hfb]
  · -- the `n`-support level is unchanged
    rw [suppVal_shift (dil_finite B (2 * K)) (dil_nonempty hfin hne (by omega)) _ n,
      suppVal_dil hfin hne (by omega) n]
    have hna : dot n a = suppVal B n := (suppVal_eq ha).symm
    have hnb : dot n b = suppVal B n := (suppVal_eq hb).symm
    have hneg : dot n (-w) = - dot n w := by
      simp only [dot, Prod.fst_neg, Prod.snd_neg]; ring
    have hdw : dot n (-w) = -(K * dot n a + (K - 1) * dot n b) := by
      rw [hneg, hw, dot_add, dot_smul_right, dot_smul_right]
    rw [hdw, hna, hnb]
    ring

/-- Same statement as `exists_enveloped_absorbing`, but also exposing the dilation parameter
`K` and the growth bound `dot m f - dot m b ≤ K` for `f ∈ F`, `m ∈ E U`, with `b ∈ B` a fixed
edge point independent of `F`.  Nothing new is proved; this is the same construction with more
of its proof term exposed, for a caller (`Nivat.AenvfixProbe.stepB`) that reuses the same `B`
across a growing sequence of `F`'s and needs to bound how `K` — and hence the size of `B₁` —
grows with `F`. -/
theorem exists_enveloped_absorbing_bounded {U B : Set (ℤ × ℤ)} {n : ℤ × ℤ}
    (hEU : (E U).Finite) (hEnv : EnvOf U B) (hfin : B.Finite) (hne : B.Nonempty)
    (harea : PosArea B) (hn : n ∈ E U) (F : Finset (ℤ × ℤ))
    (hF : ∀ f ∈ F, dot n f ≤ suppVal B n) :
    ∃ (B₁ : Set (ℤ × ℤ)) (K : ℤ) (b : ℤ × ℤ), 1 ≤ K ∧ b ∈ B ∧
      EnvOf U B₁ ∧ B ⊆ B₁ ∧ (↑F : Set (ℤ × ℤ)) ⊆ B₁ ∧
      suppVal B₁ n = suppVal B n ∧
      (∀ f ∈ F, ∀ m ∈ E U, dot m f - dot m b ≤ K) := by
  classical
  have hEB : E B = E U := Enveloped.E_eq hEU hEnv
  have hEBfin : (E B).Finite := by rw [hEB]; exact hEU
  have hnB : n ∈ E B := by rw [hEB]; exact hn
  obtain ⟨a, ha, b, hb, hab⟩ := (mem_E_iff.mp hnB).2
  set s : ℕ := (hEBfin.toFinset ×ˢ F).sup
    (fun pr => (dot pr.1 pr.2 - dot pr.1 b).toNat) with hs
  set K : ℤ := 1 + (s : ℤ) with hKdef
  have hK1 : 1 ≤ K := by
    have : (0 : ℤ) ≤ (s : ℤ) := Int.natCast_nonneg s
    omega
  have hK0 : (0 : ℤ) < 2 * K := by omega
  have hKbnd : ∀ m ∈ E B, ∀ f ∈ F, dot m f - dot m b ≤ K := by
    intro m hm f hf
    have hmem : (m, f) ∈ hEBfin.toFinset ×ˢ F :=
      Finset.mem_product.mpr ⟨hEBfin.mem_toFinset.mpr hm, hf⟩
    have hle : (dot m f - dot m b).toNat ≤ s := Finset.le_sup (f := fun pr =>
      (dot pr.1 pr.2 - dot pr.1 b).toNat) hmem
    have : dot m f - dot m b ≤ ((dot m f - dot m b).toNat : ℤ) := Int.self_le_toNat _
    have h2 : ((dot m f - dot m b).toNat : ℤ) ≤ (s : ℤ) := by exact_mod_cast hle
    omega
  set w : ℤ × ℤ := K • a + (K - 1) • b with hw
  set D : Set (ℤ × ℤ) := dil B (2 * K) with hD
  refine ⟨shift (-w) D, K, b, hK1, hb.1, ?_, ?_, ?_, ?_, ?_⟩
  · refine envOf_of_E_eq
      (isLatticeConvexRegion_shift _ (dil_isLatticeConvexRegion hfin hne harea hK0)) ?_ ?_
    · rw [E_shift, hD, E_dil hfin hne harea hK0, hEB]
    · intro m hm
      have h1 : (face U m).encard ≤ (face B m).encard :=
        Enveloped.face_encard_le hEU hEnv hm
      have h2 : (face B m).encard ≤ (face D m).encard :=
        face_encard_le_dil hfin hne hK0 m
      have h3 : (face (shift (-w) D) m).encard = (face D m).encard := by
        rw [face_shift, encard_shift]
      rw [h3]
      exact le_trans h1 h2
  · intro z hz
    show z - -w ∈ D
    have hzw : z - -w = z + w := by abel
    rw [hzw, hD]
    intro m
    have hz' : dot m z ≤ suppVal B m := le_suppVal hfin hne hz
    have ha' : dot m a ≤ suppVal B m := le_suppVal hfin hne ha.1
    have hb' : dot m b ≤ suppVal B m := le_suppVal hfin hne hb.1
    have hdw : dot m (z + w) = dot m z + K * dot m a + (K - 1) * dot m b := by
      rw [hw, dot_add, dot_add, dot_smul_right, dot_smul_right]; ring
    rw [hdw]
    have t1 : K * dot m a ≤ K * suppVal B m :=
      mul_le_mul_of_nonneg_left ha' (by omega)
    have t2 : (K - 1) * dot m b ≤ (K - 1) * suppVal B m :=
      mul_le_mul_of_nonneg_left hb' (by omega)
    have e : 2 * K * suppVal B m
        = suppVal B m + K * suppVal B m + (K - 1) * suppVal B m := by ring
    rw [e]
    linarith
  · intro f hf
    have hfF : f ∈ F := by simpa using hf
    show f - -w ∈ D
    have hzw : f - -w = f + w := by abel
    rw [hzw, hD]
    refine mem_dil_of_mem_E hfin hne harea hK0 ?_
    intro m hm
    have hdw : dot m (f + w) = dot m f + K * dot m a + (K - 1) * dot m b := by
      rw [hw, dot_add, dot_add, dot_smul_right, dot_smul_right]; ring
    rw [hdw]
    by_cases hmn : m = n
    · subst hmn
      have hna : dot m a = suppVal B m := (suppVal_eq ha).symm
      have hnb : dot m b = suppVal B m := (suppVal_eq hb).symm
      have hff : dot m f ≤ suppVal B m := hF f hfF
      have e : 2 * K * suppVal B m
          = suppVal B m + K * suppVal B m + (K - 1) * suppVal B m := by ring
      rw [e, hna, hnb]
      linarith
    · have hslack : 1 ≤ 2 * suppVal B m - dot m a - dot m b :=
        one_le_slack hfin hne harea hnB ha hb hab hm hmn
      have hfb : dot m f - dot m b ≤ K := hKbnd m hm f hfF
      have hKs : K * 1 ≤ K * (2 * suppVal B m - dot m a - dot m b) :=
        mul_le_mul_of_nonneg_left hslack (by omega)
      nlinarith [hKs, hfb]
  · rw [suppVal_shift (dil_finite B (2 * K)) (dil_nonempty hfin hne (by omega)) _ n,
      suppVal_dil hfin hne (by omega) n]
    have hna : dot n a = suppVal B n := (suppVal_eq ha).symm
    have hnb : dot n b = suppVal B n := (suppVal_eq hb).symm
    have hneg : dot n (-w) = - dot n w := by
      simp only [dot, Prod.fst_neg, Prod.snd_neg]; ring
    have hdw : dot n (-w) = -(K * dot n a + (K - 1) * dot n b) := by
      rw [hneg, hw, dot_add, dot_smul_right, dot_smul_right]
    rw [hdw, hna, hnb]
    ring
  · intro f hf m hm
    rw [← hEB] at hm
    exact hKbnd m hm f hf

/-- **Strict enlargement, as a corollary rather than an alternative.**  Absorbing anything
outside `B` makes the inclusion strict.  The converse direction does not hold: the plain
`B' ⊆ B` form is discharged by the identity witness `B := B'` and so has no content, which
is why it is not the deliverable. -/
theorem exists_enveloped_absorbing_ssubset {U B : Set (ℤ × ℤ)} {n : ℤ × ℤ}
    (hEU : (E U).Finite) (hEnv : EnvOf U B) (hfin : B.Finite) (hne : B.Nonempty)
    (harea : PosArea B) (hn : n ∈ E U) (F : Finset (ℤ × ℤ))
    (hF : ∀ f ∈ F, dot n f ≤ suppVal B n) {g : ℤ × ℤ} (hgF : g ∈ F) (hgB : g ∉ B) :
    ∃ B₁ : Set (ℤ × ℤ), EnvOf U B₁ ∧ B ⊂ B₁ ∧ (↑F : Set (ℤ × ℤ)) ⊆ B₁ ∧
      suppVal B₁ n = suppVal B n := by
  obtain ⟨B₁, henv, hsub, hFsub, hsupp⟩ :=
    exists_enveloped_absorbing hEU hEnv hfin hne harea hn F hF
  refine ⟨B₁, henv, ?_, hFsub, hsupp⟩
  rw [Set.ssubset_def]
  exact ⟨hsub, fun hc => hgB (hc (hFsub (by simpa using hgF)))⟩

/-- The same statement with `PosArea B` supplied from three distinct edges of `𝒰`, which is
how a caller holding Def 3.2's positive-area clause for `𝒰` will use it. -/
theorem exists_enveloped_absorbing_of_three_edges {U B : Set (ℤ × ℤ)}
    {n n₂ n₃ : ℤ × ℤ} (hEU : (E U).Finite) (hEnv : EnvOf U B) (hfin : B.Finite)
    (hne : B.Nonempty) (hn : n ∈ E U) (hn₂ : n₂ ∈ E U) (hn₃ : n₃ ∈ E U)
    (h12 : n ≠ n₂) (h13 : n ≠ n₃) (h23 : n₂ ≠ n₃)
    (F : Finset (ℤ × ℤ)) (hF : ∀ f ∈ F, dot n f ≤ suppVal B n) :
    ∃ B₁ : Set (ℤ × ℤ), EnvOf U B₁ ∧ B ⊆ B₁ ∧ (↑F : Set (ℤ × ℤ)) ⊆ B₁ ∧
      suppVal B₁ n = suppVal B n :=
  exists_enveloped_absorbing hEU hEnv hfin hne
    (posArea_of_envOf hn hn₂ hn₃ h12 h13 h23 hEU hEnv) hn F hF

/-! ## 8. Non-vacuity

Per the closing remark of `LatticeEdges.lean:1845` ("*everything below is a check that the
definitions are not vacuous*"): the hypotheses of `exists_enveloped_absorbing` are jointly
satisfiable by a genuine lattice polygon, and `hF` is not an accidentally unsatisfiable side
condition — the `F` below sticks out of `B` by `5` in one direction and `−4` in the other,
while one of its points sits **on** the `n`-support line (`(-4,1)`, level `1`). -/

theorem sq1_finite : (sq1 : Set (ℤ × ℤ)).Finite := by
  have hsub : (sq1 : Set (ℤ × ℤ)) ⊆ (Set.Icc (0 : ℤ) 1) ×ˢ (Set.Icc (0 : ℤ) 1) := by
    rintro z ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  exact ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _)).subset hsub

theorem suppVal_sq1_top : suppVal (sq1 : Set (ℤ × ℤ)) ((0 : ℤ), (1 : ℤ)) = 1 := by
  have hmem : ((0 : ℤ), (1 : ℤ)) ∈ face (sq1 : Set (ℤ × ℤ)) ((0 : ℤ), (1 : ℤ)) := by
    refine ⟨by simp [sq1, box], fun y hy => ?_⟩
    have h := hy.2.2.2
    simpa using h
  rw [suppVal_eq hmem]
  simp

/-- A concrete instance: `[0,1]²` absorbs `{(5,-3), (-4,1)}` inside the half plane
`{z.2 ≤ 1}` without moving the top support line. -/
theorem nonvacuous :
    ∃ B₁ : Set (ℤ × ℤ), EnvOf sq1 B₁ ∧ (sq1 : Set (ℤ × ℤ)) ⊂ B₁ ∧
      (↑({(5, -3), (-4, 1)} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) ⊆ B₁ ∧
      suppVal B₁ ((0 : ℤ), (1 : ℤ)) = suppVal (sq1 : Set (ℤ × ℤ)) ((0 : ℤ), (1 : ℤ)) := by
  refine exists_enveloped_absorbing_ssubset (U := sq1) (B := sq1) (n := ((0 : ℤ), (1 : ℤ)))
    (by rw [E_sq1]; exact Set.toFinite _)
    (enveloped_refl _ isLatticeConvexRegion_sq1)
    sq1_finite ⟨((0 : ℤ), (0 : ℤ)), by simp [sq1, box]⟩
    posArea_sq1 (by rw [E_sq1]; simp) _ ?_ (g := ((5 : ℤ), (-3 : ℤ))) (by simp) ?_
  · intro f hf
    rw [suppVal_sq1_top]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl <;> simp
  · intro hc
    simp [sq1, box] at hc

end Nivat.Absorb

#print axioms Nivat.Absorb.mem_convexHull_of_eq_max
#print axioms Nivat.Absorb.E_dil
#print axioms Nivat.Absorb.one_le_slack
#print axioms Nivat.Absorb.exists_enveloped_absorbing
#print axioms Nivat.Absorb.exists_enveloped_absorbing_bounded
#print axioms Nivat.Absorb.exists_enveloped_absorbing_ssubset
#print axioms Nivat.Absorb.exists_enveloped_absorbing_of_three_edges

#print axioms Nivat.Absorb.nonvacuous
