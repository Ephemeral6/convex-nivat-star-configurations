/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Lattice.Primitive
import Nivat.Section8.SecondHalfPlane

/-!
# §8.5. Normalisation

Formalisation of §8.5 of *The Convex Nivat Conjecture* (Pan).

An *admissible decomposition* of `ζ : ℤ² → 𝔽_p` of length `m` is a family
`(Gᵢ, hᵢ, Uᵢ, Vᵢ)_{i=1}^m` with `ζ = ∑ᵢ Gᵢ`, each `Gᵢ` of non-zero period `hᵢ` and fully
periodic on the two disjoint half-planes `Uᵢ, Vᵢ`.  Lemma 8.17 says that a non-periodic `ζ`
with an admissible decomposition *is* a star configuration — this is the bridge from §8 back to
Theorem A (§7).

The proof has three ingredients: Step (α) shows that the boundaries of `Uᵢ` and `Vᵢ` are
parallel to `hᵢ`, so that the component satisfies (S1)–(S3); Operation A absorbs a doubly
periodic component into a neighbour; Operation C merges two components with parallel periods.
Both operations shorten the decomposition, so the process terminates.

## Main results

* `Nivat.inner2_eq_zero_of_fullyPeriodic_disjoint` — **Step (α)**.
* `Nivat.exists_strip_of_admissible_component` — Step (α) in the form (S1) + (S3).
* `Nivat.exists_reduced_admissibleDecomp` — **Operations A and C**, and termination.
* `Nivat.exists_starConfig_of_admissible` — **Lemma 8.17 (Normalisation)**.

## Status

Complete; no `sorry`.
-/

namespace Nivat

open Finset

/-- An **admissible decomposition** of `ζ` of length `m`: `ζ = ∑ᵢ Gᵢ`, each `Gᵢ` with a non-zero
period `hᵢ` and fully periodic on two disjoint half-planes `Uᵢ, Vᵢ`.  Paper §8.5. -/
def AdmissibleDecomp {p : ℕ} (zeta : Config (ZMod p)) (m : ℕ) : Prop :=
  ∃ (G : Fin m → Config (ZMod p)) (h : Fin m → ℤ × ℤ) (U V : Fin m → Set (ℤ × ℤ)),
    (∀ z, zeta z = ∑ i, G i z) ∧ (∀ i, h i ≠ 0) ∧ (∀ i, h i ∈ Per (G i)) ∧
      (∀ i, IsHalfPlane (U i)) ∧ (∀ i, IsHalfPlane (V i)) ∧ (∀ i, Disjoint (U i) (V i)) ∧
      (∀ i, FullyPeriodicOn (G i) (U i)) ∧ (∀ i, FullyPeriodicOn (G i) (V i))

/-- A **reduced** admissible decomposition: in addition, no component is doubly periodic and the
periods are pairwise non-parallel.  This is the state reached at termination of Operations A
and C.  Paper §8.5. -/
def ReducedAdmissibleDecomp {p : ℕ} (zeta : Config (ZMod p)) (m : ℕ) : Prop :=
  ∃ (G : Fin m → Config (ZMod p)) (h : Fin m → ℤ × ℤ) (U V : Fin m → Set (ℤ × ℤ)),
    (∀ z, zeta z = ∑ i, G i z) ∧ (∀ i, h i ≠ 0) ∧ (∀ i, h i ∈ Per (G i)) ∧
      (∀ i, ¬ DoublyPeriodic (G i)) ∧ (Pairwise fun i j => det (h i) (h j) ≠ 0) ∧
      (∀ i, IsHalfPlane (U i)) ∧ (∀ i, IsHalfPlane (V i)) ∧ (∀ i, Disjoint (U i) (V i)) ∧
      (∀ i, FullyPeriodicOn (G i) (U i)) ∧ (∀ i, FullyPeriodicOn (G i) (V i))

theorem ReducedAdmissibleDecomp.admissible {p : ℕ} {zeta : Config (ZMod p)} {m : ℕ}
    (h : ReducedAdmissibleDecomp zeta m) : AdmissibleDecomp zeta m := by
  obtain ⟨G, hh, U, V, hsum, hne, hper, -, hnp, hU, hV, hdisj, hUfp, hVfp⟩ := h
  exact ⟨G, hh, U, V, hsum, hne, hper, hU, hV, hdisj, hUfp, hVfp⟩

/-- Since `ζ` is non-periodic, every admissible decomposition has `m ≥ 2`: for `m = 1` we would
have `ζ = G₁`, which is periodic; for `m = 0`, `ζ = 0`.  Paper §8.5. -/
theorem two_le_of_admissibleDecomp {p : ℕ} {zeta : Config (ZMod p)} {m : ℕ}
    (hnper : ¬ IsPeriodic zeta) (hd : AdmissibleDecomp zeta m) : 2 ≤ m := by
  by_contra hlt
  push Not at hlt
  obtain ⟨G, h, U, V, hsum, hne, hper, hU, hV, hdisj, hUfp, hVfp⟩ := hd
  interval_cases m
  · -- `m = 0`: `ζ ≡ 0`, which is periodic.
    refine hnper ⟨(1, 0), ?_, fun hcon => one_ne_zero (congrArg Prod.fst hcon)⟩
    rw [mem_Per_iff]
    funext z
    rw [T_apply, hsum (z + (1, 0)), hsum z, Fin.sum_univ_zero, Fin.sum_univ_zero]
  · -- `m = 1`: `ζ = G 0`, which has the non-zero period `h 0`.
    have hzeta : zeta = G 0 := by funext z; rw [hsum z, Fin.sum_univ_one]
    refine hnper ⟨h 0, ?_, hne 0⟩
    rw [mem_Per_iff, hzeta]
    exact hper 0

/-! ### Step (α): alignment -/

/-- A half-plane with non-zero normal is non-empty: translate any point far enough along a
lattice direction whose pairing with `n` is positive. -/
private theorem halfPlane_nonempty {n : ℝ × ℝ} (hn : n ≠ 0) (c : ℝ) (b : Bool) :
    (halfPlane n c b).Nonempty := by
  have hn' : n.1 ≠ 0 ∨ n.2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hn (Prod.ext hcon.1 hcon.2)
  set g0 : ℤ × ℤ := if n.1 ≠ 0 then (1, 0) else (0, 1) with hg0def
  have hg0ne : inner2 n g0 ≠ 0 := by
    rw [hg0def]
    split_ifs with h
    · simpa [inner2] using h
    · simpa [inner2] using hn'.resolve_left h
  set g : ℤ × ℤ := if 0 < inner2 n g0 then g0 else -g0 with hgdef
  have hgpos : 0 < inner2 n g := by
    rw [hgdef]
    split_ifs with h
    · exact h
    · rw [inner2_neg]
      rcases lt_or_gt_of_ne hg0ne with hlt | hgt
      · linarith
      · exact absurd hgt h
  obtain ⟨N, hN⟩ := exists_nat_gt (c / inner2 n g)
  have hc : c < (N : ℝ) * inner2 n g := (div_lt_iff₀ hgpos).mp hN
  refine ⟨N • g, ?_⟩
  rcases b with _ | _
  · show N • g ∈ {z : ℤ × ℤ | c ≤ inner2 n z}
    rw [Set.mem_ofPred_eq, inner2_nsmul]; linarith
  · show N • g ∈ {z : ℤ × ℤ | c < inner2 n z}
    rw [Set.mem_ofPred_eq, inner2_nsmul]; linarith

/-- The core of Step (α): if `⟨h, n⟩ > 0` we derive a contradiction from `G` not being doubly
periodic.  See `Nivat.inner2_eq_zero_of_fullyPeriodic_disjoint` for the full statement, which
reduces to this by replacing `h` by `−h` if necessary. -/
private theorem core_inner2_pos {p : ℕ} {G : Config (ZMod p)} {h : ℤ × ℤ}
    (_hh : h ≠ 0) (hper : h ∈ Per G) (hnd : ¬ DoublyPeriodic G)
    {n : ℝ × ℝ} (hn : n ≠ 0) {c : ℝ} {b : Bool}
    (hUfp : FullyPeriodicOn G (halfPlane n c b)) (hpos : 0 < inner2 n h) : False := by
  set U : Set (ℤ × ℤ) := halfPlane n c b with hUdef
  have hUhp : IsHalfPlane U := ⟨n, c, b, hn, rfl⟩
  have hUne : U.Nonempty := halfPlane_nonempty hn c b
  obtain ⟨h1, h2, hdet, hUh1, hUh2, hGh1, hGh2⟩ := hUfp
  have hfpw : FullyPeriodicOnWith G U h1 h2 := ⟨hdet, hUh1, hUh2, hGh1, hGh2⟩
  obtain ⟨hcov, G', hh1per, hh2per, hGdp, hGeq⟩ := exists_global_extension (Or.inr hUhp) hUne hfpw
  -- Any multiple of `h1 + h2` is a period of `G'`.
  have hcombo : ∀ K : ℕ, (K : ℤ) • (h1 + h2) ∈ Per G' := by
    intro K
    rw [smul_add]
    exact AddSubgroup.add_mem _ (AddSubgroup.zsmul_mem _ hh1per _)
      (AddSubgroup.zsmul_mem _ hh2per _)
  -- Step (α), first half: `h` is a period of `G'`.
  have hhperG' : h ∈ Per G' := by
    rw [mem_Per_iff]
    funext z
    show G' (z + h) = G' z
    obtain ⟨N₀, hN₀⟩ := hcov z
    obtain ⟨M₀, hM₀⟩ := hcov (z + h)
    set K := max N₀ M₀ with hKdef
    have hzK : z + (K : ℤ) • (h1 + h2) ∈ U := hN₀ K (le_max_left _ _)
    set w := z + (K : ℤ) • (h1 + h2) with hwdef
    have hwheq : w + h = (z + h) + (K : ℤ) • (h1 + h2) := by rw [hwdef]; abel
    have hwh : w + h ∈ U := by rw [hwheq]; exact hM₀ K (le_max_right _ _)
    have hvanish : G' (w + h) = G' w := by
      rw [hGeq (w + h) hwh, hGeq w hzK]
      exact Per.apply hper w
    have hperK : (K : ℤ) • (h1 + h2) ∈ Per G' := hcombo K
    have e1 : G' w = G' z := Per.apply hperK z
    have e2 : G' (w + h) = G' (z + h) := by rw [hwheq]; exact Per.apply hperK (z + h)
    rw [← e2, hvanish, e1]
  -- Step (α), second half: `G` and `G'` agree everywhere, so `G` is doubly periodic.
  have hGeqAll : G = G' := by
    funext z
    obtain ⟨N₀, hN₀⟩ := exists_add_nsmul_mem_halfPlane hpos hUne z
    have hzU : z + (N₀ : ℤ) • h ∈ U := hN₀ N₀ le_rfl
    have e1 : G' (z + (N₀ : ℤ) • h) = G (z + (N₀ : ℤ) • h) := hGeq _ hzU
    have e2 : G (z + (N₀ : ℤ) • h) = G z := Per.apply (AddSubgroup.zsmul_mem _ hper _) z
    have e3 : G' (z + (N₀ : ℤ) • h) = G' z := Per.apply (AddSubgroup.zsmul_mem _ hhperG' _) z
    rw [← e3, e1, e2]
  exact hnd (hGeqAll ▸ hGdp)

/-- **Step (α).**  Let `G` have a non-zero period `h`, not be doubly periodic, and be fully
periodic on disjoint half-planes `U` with normal `n` and `V`.  Then `⟨h, n⟩ = 0`.

Otherwise, after replacing `h` by `−h`, one has `⟨h, n⟩ > 0`; the global extension `Ĝ` of `G|U`
then satisfies that `Ĝ(· + h) − Ĝ` is `Per(Ĝ)`-periodic and vanishes on `U`, hence everywhere,
so `h ∈ Per(Ĝ)` and `G = Ĝ` is doubly periodic — a contradiction. -/
theorem inner2_eq_zero_of_fullyPeriodic_disjoint {p : ℕ} {G : Config (ZMod p)} {h : ℤ × ℤ}
    (hh : h ≠ 0) (hper : h ∈ Per G) (hnd : ¬ DoublyPeriodic G)
    {n : ℝ × ℝ} (hn : n ≠ 0) {c : ℝ} {b : Bool}
    (hUfp : FullyPeriodicOn G (halfPlane n c b)) {V : Set (ℤ × ℤ)} (_hV : IsHalfPlane V)
    (_hVfp : FullyPeriodicOn G V) (_hdisj : Disjoint (halfPlane n c b) V) :
    inner2 n h = 0 := by
  by_contra hne0
  rcases lt_or_gt_of_ne hne0 with hlt | hgt
  · exact core_inner2_pos (neg_ne_zero.mpr hh) ((Per G).neg_mem hper) hnd hn hUfp
      (by rw [inner2_neg]; linarith)
  · exact core_inner2_pos hh hper hnd hn hUfp hgt

/-- If a half-plane's normal is orthogonal to a non-zero vector `h = kv` (`v` primitive), then in
the `π_v`-coordinate the half-plane is exactly of the form `{π_v > r}` or `{π_v < ℓ}`. -/
private theorem sided_of_inner2_eq_zero {n : ℝ × ℝ} (hn : n ≠ 0) (c : ℝ) (b : Bool)
    {v u h : ℤ × ℤ} (hvu : det v u = 1) {k : ℕ} (hk : 0 < k) (hhv : h = (k : ℤ) • v)
    (hperp : inner2 n h = 0) :
    (∃ r : ℤ, ∀ z, r < pi v z → z ∈ halfPlane n c b) ∨
      (∃ ell : ℤ, ∀ z, pi v z < ell → z ∈ halfPlane n c b) := by
  have hnv : inner2 n v = 0 := by
    rw [hhv, inner2_zsmul] at hperp
    have hkne : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    exact (mul_eq_zero.mp hperp).resolve_left hkne
  set m : ℝ := inner2 n u with hmdef
  have hmne : m ≠ 0 := by
    intro hm0
    apply hn
    have he1 : (1, 0) = (det (1, 0) u) • v + (det v (1, 0)) • u := eq_smul_add_smul hvu (1, 0)
    have he2 : (0, 1) = (det (0, 1) u) • v + (det v (0, 1)) • u := eq_smul_add_smul hvu (0, 1)
    have hn1 : n.1 = 0 := by
      have h1 : inner2 n (1, 0) = 0 := by
        rw [he1, inner2_add, inner2_zsmul, inner2_zsmul, hnv, ← hmdef, hm0]; ring
      simpa [inner2] using h1
    have hn2 : n.2 = 0 := by
      have h2 : inner2 n (0, 1) = 0 := by
        rw [he2, inner2_add, inner2_zsmul, inner2_zsmul, hnv, ← hmdef, hm0]; ring
      simpa [inner2] using h2
    exact Prod.ext hn1 hn2
  have hzform : ∀ z : ℤ × ℤ, inner2 n z = (pi v z : ℝ) * m := by
    intro z
    have hz : z = (det z u) • v + (det v z) • u := eq_smul_add_smul hvu z
    have hcalc : inner2 n z = (det z u : ℝ) * inner2 n v + (det v z : ℝ) * inner2 n u := by
      conv_lhs => rw [hz]
      rw [inner2_add, inner2_zsmul, inner2_zsmul]
    rw [hcalc, hnv, hmdef]
    show (det z u : ℝ) * 0 + (det v z : ℝ) * inner2 n u = (pi v z : ℝ) * inner2 n u
    have hpi : pi v z = det v z := rfl
    rw [hpi]; ring
  rcases lt_or_gt_of_ne hmne with hlt | hgt
  · -- `m < 0`: the half-plane is `{π_v < ⌊c / m⌋}`.
    refine Or.inr ⟨⌊c / m⌋, fun z hz => ?_⟩
    have hzm : (⌊c / m⌋ : ℝ) ≤ c / m := Int.floor_le _
    have hlt' : (pi v z : ℝ) < (⌊c / m⌋ : ℝ) := by exact_mod_cast hz
    have hcm : (pi v z : ℝ) < c / m := lt_of_lt_of_le hlt' hzm
    have hkey : c < (pi v z : ℝ) * m := (lt_div_iff_of_neg hlt).mp hcm
    show z ∈ halfPlane n c b
    rcases b with _ | _
    · show z ∈ {z : ℤ × ℤ | c ≤ inner2 n z}
      rw [Set.mem_ofPred_eq, hzform]; linarith
    · show z ∈ {z : ℤ × ℤ | c < inner2 n z}
      rw [Set.mem_ofPred_eq, hzform]; linarith
  · -- `m > 0`: the half-plane is `{π_v > ⌈c / m⌉}`.
    refine Or.inl ⟨⌈c / m⌉, fun z hz => ?_⟩
    have hzm : c / m ≤ (⌈c / m⌉ : ℝ) := Int.le_ceil _
    have hlt' : (⌈c / m⌉ : ℝ) < (pi v z : ℝ) := by exact_mod_cast hz
    have hcm : c / m < (pi v z : ℝ) := lt_of_le_of_lt hzm hlt'
    have hkey : c < (pi v z : ℝ) * m := (div_lt_iff₀ hgt).mp hcm
    show z ∈ halfPlane n c b
    rcases b with _ | _
    · show z ∈ {z : ℤ × ℤ | c ≤ inner2 n z}
      rw [Set.mem_ofPred_eq, hzform]; linarith
    · show z ∈ {z : ℤ × ℤ | c < inner2 n z}
      rw [Set.mem_ofPred_eq, hzform]; linarith

/-- **Step (α)**, in the form of the star-configuration axioms.  A component of an admissible
decomposition which is not doubly periodic satisfies (S1), (S2) and (S3): writing `h = kv` with
`v` primitive and `k ≥ 1` (after a sign change) and `φ = π_v`, the two half-planes are
`{φ < ℓ}` and `{φ > r}` with `ℓ ≤ r + 1`, and `G` agrees there with the doubly periodic global
extensions `L` and `R` of Lemma 8.2. -/
theorem exists_strip_of_admissible_component {p : ℕ} {G : Config (ZMod p)} {h : ℤ × ℤ}
    (hh : h ≠ 0) (hper : h ∈ Per G) (hnd : ¬ DoublyPeriodic G)
    {U V : Set (ℤ × ℤ)} (hU : IsHalfPlane U) (hV : IsHalfPlane V) (hdisj : Disjoint U V)
    (hUfp : FullyPeriodicOn G U) (hVfp : FullyPeriodicOn G V) :
    ∃ (v : ℤ × ℤ) (k : ℕ) (L R : Config (ZMod p)) (ell r : ℤ),
      Primitive v ∧ 0 < k ∧ det v h = 0 ∧ ((k : ℤ) • v) ∈ Per G ∧
        DoublyPeriodic L ∧ DoublyPeriodic R ∧ ell ≤ r + 1 ∧
        (∀ z, pi v z < ell → G z = L z) ∧ (∀ z, r < pi v z → G z = R z) := by
  obtain ⟨v, k, hvprim, hk, hhv⟩ := exists_primitive_nsmul_eq hh
  obtain ⟨u, hvu⟩ := hvprim.exists_dual
  have hvh : det v h = 0 := by
    rw [hhv]; show det v ((k : ℤ) • v) = 0
    simp only [det, Prod.smul_def, smul_eq_mul]; ring
  have hkvper : ((k : ℤ) • v) ∈ Per G := hhv ▸ hper
  -- Global extensions of `G` on `U` and on `V`.
  obtain ⟨nU, cU, bU, hnU, hUeq⟩ := hU
  obtain ⟨nV, cV, bV, hnV, hVeq⟩ := hV
  obtain ⟨h1U, h2U, hdetU, hUh1, hUh2, hGh1U, hGh2U⟩ := hUfp
  obtain ⟨h1V, h2V, hdetV, hVh1, hVh2, hGh1V, hGh2V⟩ := hVfp
  have hUne : U.Nonempty := hUeq ▸ halfPlane_nonempty hnU cU bU
  have hVne : V.Nonempty := hVeq ▸ halfPlane_nonempty hnV cV bV
  have hfpU : FullyPeriodicOnWith G U h1U h2U := ⟨hdetU, hUh1, hUh2, hGh1U, hGh2U⟩
  have hfpV : FullyPeriodicOnWith G V h1V h2V := ⟨hdetV, hVh1, hVh2, hGh1V, hGh2V⟩
  obtain ⟨-, GU, -, -, hGUdp, hGUeq⟩ :=
    exists_global_extension (show IsLatticeConvexRegion U ∨ IsHalfPlane U from
      Or.inr ⟨nU, cU, bU, hnU, hUeq⟩) hUne hfpU
  obtain ⟨-, GV, -, -, hGVdp, hGVeq⟩ :=
    exists_global_extension (show IsLatticeConvexRegion V ∨ IsHalfPlane V from
      Or.inr ⟨nV, cV, bV, hnV, hVeq⟩) hVne hfpV
  -- Step (α) applied to `U` (against `V`) and to `V` (against `U`).
  have hUfpHP : FullyPeriodicOn G (halfPlane nU cU bU) := by
    rw [← hUeq]; exact ⟨h1U, h2U, hfpU⟩
  have hVfpHP : FullyPeriodicOn G (halfPlane nV cV bV) := by
    rw [← hVeq]; exact ⟨h1V, h2V, hfpV⟩
  have hUfpV : FullyPeriodicOn G U := ⟨h1U, h2U, hfpU⟩
  have hVfpV : FullyPeriodicOn G V := ⟨h1V, h2V, hfpV⟩
  have hdisjU : Disjoint (halfPlane nU cU bU) V := by rw [← hUeq]; exact hdisj
  have hdisjV : Disjoint (halfPlane nV cV bV) U := by rw [← hVeq]; exact hdisj.symm
  have hperpU : inner2 nU h = 0 :=
    inner2_eq_zero_of_fullyPeriodic_disjoint hh hper hnd hnU hUfpHP
      ⟨nV, cV, bV, hnV, hVeq⟩ hVfpV hdisjU
  have hperpV : inner2 nV h = 0 :=
    inner2_eq_zero_of_fullyPeriodic_disjoint hh hper hnd hnV hVfpHP
      ⟨nU, cU, bU, hnU, hUeq⟩ hUfpV hdisjV
  have hsideU := sided_of_inner2_eq_zero hnU cU bU hvu hk hhv hperpU
  have hsideV := sided_of_inner2_eq_zero hnV cV bV hvu hk hhv hperpV
  -- Translate membership in `U`/`V` back to `G = GU`/`G = GV`.
  have hGU : ∀ z ∈ U, G z = GU z := fun z hz => (hGUeq z hz).symm
  have hGV : ∀ z ∈ V, G z = GV z := fun z hz => (hGVeq z hz).symm
  -- A point realising any prescribed value of `π_v` exists.
  have hsurj : Function.Surjective (pi v) := pi_surjective hvprim
  rcases hsideU with ⟨rU, hrU⟩ | ⟨ellU, hellU⟩ <;> rcases hsideV with ⟨rV, hrV⟩ | ⟨ellV, hellV⟩
  · -- both "high": contradiction, `U` and `V` overlap far along `π_v`.
    exfalso
    obtain ⟨z0, hz0⟩ := hsurj (max rU rV + 1)
    have h1 : z0 ∈ U := by rw [hUeq]; exact hrU z0 (by rw [hz0]; omega)
    have h2 : z0 ∈ V := by rw [hVeq]; exact hrV z0 (by rw [hz0]; omega)
    exact (Set.disjoint_left.mp hdisj h1) h2
  · -- `U` high (`rU`), `V` low (`ellV`): `L := GV`, `R := GU`.
    refine ⟨v, k, GV, GU, ellV, rU, hvprim, hk, hvh, hkvper, hGVdp, hGUdp, ?_, ?_, ?_⟩
    · by_contra hcon
      push Not at hcon
      obtain ⟨z0, hz0⟩ := hsurj (rU + 1)
      have h1 : z0 ∈ U := by rw [hUeq]; exact hrU z0 (by rw [hz0]; omega)
      have h2 : z0 ∈ V := by rw [hVeq]; exact hellV z0 (by rw [hz0]; omega)
      exact (Set.disjoint_left.mp hdisj h1) h2
    · intro z hz; exact hGV z (by rw [hVeq]; exact hellV z hz)
    · intro z hz; exact hGU z (by rw [hUeq]; exact hrU z hz)
  · -- `U` low (`ellU`), `V` high (`rV`): `L := GU`, `R := GV`.
    refine ⟨v, k, GU, GV, ellU, rV, hvprim, hk, hvh, hkvper, hGUdp, hGVdp, ?_, ?_, ?_⟩
    · by_contra hcon
      push Not at hcon
      obtain ⟨z0, hz0⟩ := hsurj (rV + 1)
      have h1 : z0 ∈ V := by rw [hVeq]; exact hrV z0 (by rw [hz0]; omega)
      have h2 : z0 ∈ U := by rw [hUeq]; exact hellU z0 (by rw [hz0]; omega)
      exact (Set.disjoint_left.mp hdisj h2) h1
    · intro z hz; exact hGU z (by rw [hUeq]; exact hellU z hz)
    · intro z hz; exact hGV z (by rw [hVeq]; exact hrV z hz)
  · -- both "low": contradiction, symmetric to the first case.
    exfalso
    obtain ⟨z0, hz0⟩ := hsurj (min ellU ellV - 1)
    have h1 : z0 ∈ U := by rw [hUeq]; exact hellU z0 (by rw [hz0]; omega)
    have h2 : z0 ∈ V := by rw [hVeq]; exact hellV z0 (by rw [hz0]; omega)
    exact (Set.disjoint_left.mp hdisj h1) h2


/-! ### Operations A and C -/

/-- A common period of two configurations is a period of their sum. -/
private theorem Per.add_mem' {p : ℕ} {f g : Config (ZMod p)} {u : ℤ × ℤ}
    (hf : u ∈ Per f) (hg : u ∈ Per g) : u ∈ Per (fun z => f z + g z) := by
  rw [mem_Per_iff]
  funext z
  show f (z + u) + g (z + u) = f z + g z
  rw [Per.apply hf z, Per.apply hg z]

/-- If `G` is fully periodic on a half-plane `U` and `Gd` is doubly periodic, then `G + Gd` is
fully periodic on `U`: scale a pair of witnesses for `G` on `U` by a common multiple that also
lands in `Per Gd`.  Used by Operation A. -/
private theorem fullyPeriodicOn_add_of_doublyPeriodic {p : ℕ} {G Gd : Config (ZMod p)}
    {U : Set (ℤ × ℤ)} (hU : IsHalfPlane U) (hfp : FullyPeriodicOn G U) (hd : DoublyPeriodic Gd) :
    FullyPeriodicOn (fun z => G z + Gd z) U := by
  obtain ⟨n, c, b, hn, hUeq⟩ := hU
  subst hUeq
  obtain ⟨a, a', hdet, hUa, hUa', hGa, hGa'⟩ := hfp
  obtain ⟨N, hN, hNmem⟩ := hd.exists_smul_mem
  set M : ℕ := N.natAbs with hMdef
  have hMne : (M : ℤ) ≠ 0 := by
    simp only [hMdef]; exact_mod_cast Int.natAbs_ne_zero.mpr hN
  have hMa_perGd : (M : ℤ) • a ∈ Per Gd := by
    rcases Int.natAbs_eq N with hNeq | hNeq
    · rw [hMdef, ← hNeq]; exact hNmem a
    · have hcast : (M : ℤ) = -N := by rw [hMdef]; linarith [hNeq]
      rw [hcast, neg_smul]; exact (Per Gd).neg_mem (hNmem a)
  have hMa'_perGd : (M : ℤ) • a' ∈ Per Gd := by
    rcases Int.natAbs_eq N with hNeq | hNeq
    · rw [hMdef, ← hNeq]; exact hNmem a'
    · have hcast : (M : ℤ) = -N := by rw [hMdef]; linarith [hNeq]
      rw [hcast, neg_smul]; exact (Per Gd).neg_mem (hNmem a')
  have hne : (halfPlane n c b).Nonempty := halfPlane_nonempty hn c b
  have hna : 0 ≤ inner2 n a := inner2_nonneg_of_halfPlane_add_subset hne hUa
  have hna' : 0 ≤ inner2 n a' := inner2_nonneg_of_halfPlane_add_subset hne hUa'
  have hpreserve : ∀ (K : ℕ) (w : ℤ × ℤ), w ∈ halfPlane n c b → w + (K : ℤ) • a ∈ halfPlane n c b :=
    fun K w hw => halfPlane_add_subset
      (by rw [inner2_zsmul]; exact mul_nonneg (by exact_mod_cast Nat.zero_le K) hna) ⟨w, hw, rfl⟩
  have hpreserve' : ∀ (K : ℕ) (w : ℤ × ℤ),
      w ∈ halfPlane n c b → w + (K : ℤ) • a' ∈ halfPlane n c b :=
    fun K w hw => halfPlane_add_subset
      (by rw [inner2_zsmul]; exact mul_nonneg (by exact_mod_cast Nat.zero_le K) hna') ⟨w, hw, rfl⟩
  have hGnsmul : ∀ (K : ℕ) (w : ℤ × ℤ), w ∈ halfPlane n c b → G (w + (K : ℤ) • a) = G w := by
    intro K
    induction K with
    | zero => intro w _; simp
    | succ k ih =>
      intro w hw
      have hwk : w + (k : ℤ) • a ∈ halfPlane n c b := hpreserve k w hw
      have hstep : G (w + (k : ℤ) • a + a) = G (w + (k : ℤ) • a) := hGa _ hwk
      have heq : w + ((k : ℕ) + 1 : ℤ) • a = w + (k : ℤ) • a + a := by
        rw [add_smul, one_smul]; abel
      rw [show ((k + 1 : ℕ) : ℤ) = ((k : ℕ) + 1 : ℤ) by push_cast; ring, heq, hstep, ih w hw]
  have hG'nsmul : ∀ (K : ℕ) (w : ℤ × ℤ), w ∈ halfPlane n c b → G (w + (K : ℤ) • a') = G w := by
    intro K
    induction K with
    | zero => intro w _; simp
    | succ k ih =>
      intro w hw
      have hwk : w + (k : ℤ) • a' ∈ halfPlane n c b := hpreserve' k w hw
      have hstep : G (w + (k : ℤ) • a' + a') = G (w + (k : ℤ) • a') := hGa' _ hwk
      have heq : w + ((k : ℕ) + 1 : ℤ) • a' = w + (k : ℤ) • a' + a' := by
        rw [add_smul, one_smul]; abel
      rw [show ((k + 1 : ℕ) : ℤ) = ((k : ℕ) + 1 : ℤ) by push_cast; ring, heq, hstep, ih w hw]
  refine ⟨(M : ℤ) • a, (M : ℤ) • a', ?_, ?_, ?_, ?_, ?_⟩
  · rw [det_zsmul_zsmul]; exact mul_ne_zero (mul_ne_zero hMne hMne) hdet
  · exact fun w hw => hpreserve M w hw
  · exact fun w hw => hpreserve' M w hw
  · intro w hw
    show G (w + (M : ℤ) • a) + Gd (w + (M : ℤ) • a) = G w + Gd w
    rw [hGnsmul M w hw, Per.apply hMa_perGd w]
  · intro w hw
    show G (w + (M : ℤ) • a') + Gd (w + (M : ℤ) • a') = G w + Gd w
    rw [hG'nsmul M w hw, Per.apply hMa'_perGd w]

/-- **Operation A (absorbing a doubly periodic component).**  If `Gᵢ` is doubly periodic and
`m ≥ 2`, pick `k ≠ i`; since `Per(Gᵢ)` has finite index, `Per(Gᵢ) ∩ ℤhₖ` contains a non-zero
`h'ₖ`, and `G'ₖ = Gₖ + Gᵢ` has period `h'ₖ` and is fully periodic on `Uₖ` and on `Vₖ`.  Deleting
`Gᵢ` shortens the decomposition by one. -/
theorem exists_admissibleDecomp_of_doublyPeriodic_component {p : ℕ} {zeta : Config (ZMod p)}
    {m : ℕ} (hm : 2 ≤ m) {G : Fin m → Config (ZMod p)} {h : Fin m → ℤ × ℤ}
    {U V : Fin m → Set (ℤ × ℤ)}
    (hsum : ∀ z, zeta z = ∑ i, G i z) (hne : ∀ i, h i ≠ 0) (hper : ∀ i, h i ∈ Per (G i))
    (hU : ∀ i, IsHalfPlane (U i)) (hV : ∀ i, IsHalfPlane (V i))
    (hdisj : ∀ i, Disjoint (U i) (V i))
    (hUfp : ∀ i, FullyPeriodicOn (G i) (U i)) (hVfp : ∀ i, FullyPeriodicOn (G i) (V i))
    {i : Fin m} (hi : DoublyPeriodic (G i)) : AdmissibleDecomp zeta (m - 1) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  subst hn
  show AdmissibleDecomp zeta n
  set z0 : Fin n := ⟨0, by omega⟩ with hz0def
  set k : Fin (n + 1) := i.succAbove z0 with hkdef
  have hki : k ≠ i := i.succAbove_ne z0
  -- A non-zero common period of `G k` and `G i`.
  obtain ⟨N, hN, hNmem⟩ := hi.exists_smul_mem
  set hk' : ℤ × ℤ := N • h k with hk'def
  have hk'ne : hk' ≠ 0 := hk'def ▸ zsmul_ne_zero_of_ne_zero hN (hne k)
  have hk'perGk : hk' ∈ Per (G k) := hk'def ▸ AddSubgroup.zsmul_mem _ (hper k) N
  have hk'perGi : hk' ∈ Per (G i) := hk'def ▸ hNmem (h k)
  have hk'perSum : hk' ∈ Per (fun z => G k z + G i z) := Per.add_mem' hk'perGk hk'perGi
  have hUcomb : FullyPeriodicOn (fun z => G k z + G i z) (U k) :=
    fullyPeriodicOn_add_of_doublyPeriodic (hU k) (hUfp k) hi
  have hVcomb : FullyPeriodicOn (fun z => G k z + G i z) (V k) :=
    fullyPeriodicOn_add_of_doublyPeriodic (hV k) (hVfp k) hi
  refine ⟨fun j z => G (i.succAbove j) z + (if j = z0 then G i z else 0),
    fun j => if j = z0 then hk' else h (i.succAbove j),
    fun j => if j = z0 then U k else U (i.succAbove j),
    fun j => if j = z0 then V k else V (i.succAbove j),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    have hz := hsum z
    rw [Fin.sum_univ_succAbove (fun l => G l z) i] at hz
    rw [hz, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ z0 (fun _ => G i z),
      if_pos (Finset.mem_univ z0)]
    abel
  · intro j
    by_cases hj : j = z0
    · simp only [hj, if_true]; exact hk'ne
    · simp only [hj, if_false]; exact hne (i.succAbove j)
  · intro j
    by_cases hj : j = z0
    · simp only [hj, if_true]; exact hk'perSum
    · simp only [hj, if_false, add_zero]; exact hper (i.succAbove j)
  · intro j
    by_cases hj : j = z0
    · simp only [hj, if_true]; exact hU k
    · simp only [hj, if_false]; exact hU (i.succAbove j)
  · intro j
    by_cases hj : j = z0
    · simp only [hj, if_true]; exact hV k
    · simp only [hj, if_false]; exact hV (i.succAbove j)
  · intro j
    by_cases hj : j = z0
    · simp only [hj, if_true]; exact hdisj k
    · simp only [hj, if_false]; exact hdisj (i.succAbove j)
  · intro j
    by_cases hj : j = z0
    · simp only [hj, if_true]; exact hUcomb
    · simp only [hj, if_false, add_zero]; exact hUfp (i.succAbove j)
  · intro j
    by_cases hj : j = z0
    · simp only [hj, if_true]; exact hVcomb
    · simp only [hj, if_false, add_zero]; exact hVfp (i.succAbove j)

/-- `inner2` is negated by negating the first argument. -/
private theorem inner2_neg_left (n : ℝ × ℝ) (a : ℤ × ℤ) : inner2 n (-a) = -inner2 n a := by
  simp only [inner2, Prod.fst_neg, Prod.snd_neg]; push_cast; ring

/-- The sum of two doubly periodic configurations is doubly periodic: a common non-zero
multiple of a period of each pair `(N, M)` gives a full-rank pair of periods of the sum. -/
private theorem doublyPeriodic_add {p : ℕ} {f g : Config (ZMod p)}
    (hf : DoublyPeriodic f) (hg : DoublyPeriodic g) :
    DoublyPeriodic (fun z => f z + g z) := by
  obtain ⟨N, hN, hNmem⟩ := hf.exists_smul_mem
  obtain ⟨M, hM, hMmem⟩ := hg.exists_smul_mem
  set L : ℤ := N * M with hLdef
  have hLne : L ≠ 0 := mul_ne_zero hN hM
  have hLf : ∀ z, L • z ∈ Per f := by
    intro z
    have heq : L • z = M • (N • z) := by rw [hLdef, mul_comm, mul_smul]
    rw [heq]; exact AddSubgroup.zsmul_mem _ (hNmem z) M
  have hLg : ∀ z, L • z ∈ Per g := by
    intro z
    have heq : L • z = N • (M • z) := by rw [hLdef, mul_smul]
    rw [heq]; exact AddSubgroup.zsmul_mem _ (hMmem z) N
  have hd1 : det ((1 : ℤ), (0 : ℤ)) (0, 1) = 1 := by simp [det]
  refine ⟨L • ((1 : ℤ), (0 : ℤ)), Per.add_mem' (hLf _) (hLg _),
    L • ((0 : ℤ), (1 : ℤ)), Per.add_mem' (hLf _) (hLg _), ?_⟩
  rw [det_zsmul_zsmul, hd1, mul_one]
  exact mul_ne_zero hLne hLne

/-- If `k1 ∣ L` (as naturals) and `k1 • v` is a period, so is `L • v`. -/
private theorem zsmul_mem_of_dvd {p : ℕ} {G : Config (ZMod p)} {v : ℤ × ℤ} {k1 L : ℕ}
    (hdvd : k1 ∣ L) (hmem : (k1 : ℤ) • v ∈ Per G) : (L : ℤ) • v ∈ Per G := by
  obtain ⟨c, hc⟩ := hdvd
  have hcast : (L : ℤ) = (c : ℤ) * (k1 : ℤ) := by rw [hc]; push_cast; ring
  have heq : (L : ℤ) • v = (c : ℤ) • ((k1 : ℤ) • v) := by rw [smul_smul, ← hcast]
  rw [heq]; exact AddSubgroup.zsmul_mem _ hmem c

/-- Rewriting `{z | pi v z < ell}` as a rational half-plane. -/
private theorem isHalfPlane_pi_lt {v : ℤ × ℤ} (hv : v ≠ 0) (ell : ℤ) :
    IsHalfPlane {z | pi v z < ell} := by
  have hset : {z : ℤ × ℤ | pi v z < ell} = latHalfPlane false v (1 - ell) := by
    ext z
    simp [latHalfPlane, piE]
    omega
  rw [hset]; exact isHalfPlane_latHalfPlane hv false (1 - ell)

/-- Rewriting `{z | r < pi v z}` as a rational half-plane. -/
private theorem isHalfPlane_pi_gt {v : ℤ × ℤ} (hv : v ≠ 0) (r : ℤ) :
    IsHalfPlane {z | r < pi v z} := by
  have hset : {z : ℤ × ℤ | r < pi v z} = latHalfPlane true v (r + 1) := by
    ext z
    simp [latHalfPlane, piE]
  rw [hset]; exact isHalfPlane_latHalfPlane hv true (r + 1)

/-- If `G` agrees with a doubly periodic `Ld` on a half-plane `U`, then `G` is fully periodic on
`U`: flip the sign of a pair of periods of `Ld` so that both preserve `U`, using that `U`'s
translations by non-negatively paired vectors stay inside `U`. -/
private theorem fullyPeriodicOn_of_eqOn_doublyPeriodic {p : ℕ} {G Ld : Config (ZMod p)}
    {U : Set (ℤ × ℤ)} (hU : IsHalfPlane U) (hd : DoublyPeriodic Ld)
    (heq : ∀ z ∈ U, G z = Ld z) : FullyPeriodicOn G U := by
  obtain ⟨n, c, b, hn, hUeq⟩ := hU
  subst hUeq
  obtain ⟨a, ha, a', ha', hdet⟩ := hd
  set e1 : ℤ := if 0 ≤ inner2 n a then 1 else -1 with he1def
  set e2 : ℤ := if 0 ≤ inner2 n a' then 1 else -1 with he2def
  set a1 : ℤ × ℤ := e1 • a with ha1def
  set a1' : ℤ × ℤ := e2 • a' with ha1'def
  have he1ne : e1 ≠ 0 := by rw [he1def]; split_ifs <;> norm_num
  have he2ne : e2 ≠ 0 := by rw [he2def]; split_ifs <;> norm_num
  have ha1per : a1 ∈ Per Ld := ha1def ▸ AddSubgroup.zsmul_mem _ ha e1
  have ha1'per : a1' ∈ Per Ld := ha1'def ▸ AddSubgroup.zsmul_mem _ ha' e2
  have hna1 : 0 ≤ inner2 n a1 := by
    rw [ha1def, inner2_zsmul, he1def]
    split_ifs with h
    · simpa using h
    · rw [not_le] at h; push_cast; nlinarith
  have hna1' : 0 ≤ inner2 n a1' := by
    rw [ha1'def, inner2_zsmul, he2def]
    split_ifs with h
    · simpa using h
    · rw [not_le] at h; push_cast; nlinarith
  have hdet1 : det a1 a1' ≠ 0 := by
    rw [ha1def, ha1'def, det_zsmul_zsmul]
    exact mul_ne_zero (mul_ne_zero he1ne he2ne) hdet
  have hUa1 : (fun z => z + a1) '' halfPlane n c b ⊆ halfPlane n c b := halfPlane_add_subset hna1
  have hUa1' : (fun z => z + a1') '' halfPlane n c b ⊆ halfPlane n c b := halfPlane_add_subset hna1'
  refine ⟨a1, a1', hdet1, fun z hz => hUa1 ⟨z, hz, rfl⟩, fun z hz => hUa1' ⟨z, hz, rfl⟩, ?_, ?_⟩
  · intro z hz
    have hz' : z + a1 ∈ halfPlane n c b := hUa1 ⟨z, hz, rfl⟩
    rw [heq _ hz', heq _ hz, Per.apply ha1per z]
  · intro z hz
    have hz' : z + a1' ∈ halfPlane n c b := hUa1' ⟨z, hz, rfl⟩
    rw [heq _ hz', heq _ hz, Per.apply ha1'per z]

/-- **Operation C (merging parallel components).**  If `Gᵢ, Gₖ` with `i ≠ k` are both not doubly
periodic and `hᵢ ∥ hₖ`, then by Step (α) both pairs of half-planes are bounded by lines parallel
to the common primitive direction `v`, and `Gᵢ + Gₖ` has period `lcm(kᵢ, kₖ)v` and is fully
periodic on `{φ < min(ℓᵢ, ℓₖ)}` and `{φ > max(rᵢ, rₖ)}`, which are disjoint.  Merging shortens
the decomposition by one. -/
theorem exists_admissibleDecomp_of_parallel {p : ℕ} {zeta : Config (ZMod p)} {m : ℕ}
    (hm : 2 ≤ m) {G : Fin m → Config (ZMod p)} {h : Fin m → ℤ × ℤ}
    {U V : Fin m → Set (ℤ × ℤ)}
    (hsum : ∀ z, zeta z = ∑ i, G i z) (hne : ∀ i, h i ≠ 0) (hper : ∀ i, h i ∈ Per (G i))
    (hU : ∀ i, IsHalfPlane (U i)) (hV : ∀ i, IsHalfPlane (V i))
    (hdisj : ∀ i, Disjoint (U i) (V i))
    (hUfp : ∀ i, FullyPeriodicOn (G i) (U i)) (hVfp : ∀ i, FullyPeriodicOn (G i) (V i))
    (hnd : ∀ i, ¬ DoublyPeriodic (G i))
    {i k : Fin m} (hik : i ≠ k) (hpar : det (h i) (h k) = 0) :
    AdmissibleDecomp zeta (m - 1) := by
  -- Step (α) applied to both components, in the (S1)+(S3) form.
  obtain ⟨v, k1, Li, Ri, elli, ri, hvprim, hk1, hviperp, hk1vperGi, hLidp, hRidp, helliri, hGiL,
    hGiR⟩ := exists_strip_of_admissible_component (hne i) (hper i) (hnd i) (hU i) (hV i)
      (hdisj i) (hUfp i) (hVfp i)
  obtain ⟨w, k2, Lk, Rk, ellk, rk, hwprim, hk2, hwperp, hk2wperGk, hLkdp, hRkdp, hellkrk, hGkL,
    hGkR⟩ := exists_strip_of_admissible_component (hne k) (hper k) (hnd k) (hU k) (hV k)
      (hdisj k) (hUfp k) (hVfp k)
  -- `h i` is orthogonal to `v` and `h k` to `w`, so `h i, h k` are non-zero multiples of `v, w`.
  obtain ⟨ci, hci⟩ := eq_zsmul_of_det_eq_zero hvprim hviperp
  obtain ⟨ck, hck⟩ := eq_zsmul_of_det_eq_zero hwprim hwperp
  have hcine : ci ≠ 0 := fun hcon => hne i (by rw [hci, hcon, zero_smul])
  have hckne : ck ≠ 0 := fun hcon => hne k (by rw [hck, hcon, zero_smul])
  have hcompute : det (h i) (h k) = ci * ck * det v w := by rw [hci, hck, det_zsmul_zsmul]
  have heq0 : ci * ck * det v w = 0 := by rw [← hcompute, hpar]
  have hdetvw : det v w = 0 := (mul_eq_zero.mp heq0).resolve_left (mul_ne_zero hcine hckne)
  -- Hence `v` and `w` are equal or opposite: normalise everything to `v`.
  have hwv : w = v ∨ w = -v := eq_or_eq_neg_of_det_eq_zero hvprim hwprim hdetvw
  have hk2vperGk : (k2 : ℤ) • v ∈ Per (G k) := by
    rcases hwv with rfl | rfl
    · exact hk2wperGk
    · have heq : (k2 : ℤ) • (-v) = -((k2 : ℤ) • v) := smul_neg _ _
      rw [heq] at hk2wperGk
      simpa using (Per (G k)).neg_mem hk2wperGk
  obtain ⟨Lk', Rk', ellk', rk', hLk'dp, hRk'dp, hellk'rk', hGkL', hGkR'⟩ :
      ∃ (Lk' Rk' : Config (ZMod p)) (ellk' rk' : ℤ), DoublyPeriodic Lk' ∧ DoublyPeriodic Rk' ∧
        ellk' ≤ rk' + 1 ∧ (∀ z, pi v z < ellk' → G k z = Lk' z) ∧
          (∀ z, rk' < pi v z → G k z = Rk' z) := by
    rcases hwv with rfl | rfl
    · exact ⟨Lk, Rk, ellk, rk, hLkdp, hRkdp, hellkrk, hGkL, hGkR⟩
    · refine ⟨Rk, Lk, -rk, -ellk, hRkdp, hLkdp, by omega, ?_, ?_⟩
      · intro z hz
        apply hGkR
        have hpiw : pi (-v) z = -pi v z := pi_neg_left v z
        omega
      · intro z hz
        apply hGkL
        have hpiw : pi (-v) z = -pi v z := pi_neg_left v z
        omega
  -- A common non-zero period `L • v` of `G i + G k`, `L := k1 * k2`.
  set L : ℕ := k1 * k2 with hLdef
  have hLpos : 0 < L := mul_pos hk1 hk2
  have hLvne : (L : ℤ) • v ≠ 0 :=
    zsmul_ne_zero_of_ne_zero (by exact_mod_cast hLpos.ne') hvprim.ne_zero
  have hLvperGi : (L : ℤ) • v ∈ Per (G i) :=
    zsmul_mem_of_dvd (by rw [hLdef]; exact dvd_mul_right k1 k2) hk1vperGi
  have hLvperGk : (L : ℤ) • v ∈ Per (G k) :=
    zsmul_mem_of_dvd (by rw [hLdef]; exact dvd_mul_left k2 k1) hk2vperGk
  have hLvperSum : (L : ℤ) • v ∈ Per (fun z => G i z + G k z) := Per.add_mem' hLvperGi hLvperGk
  -- The merged strip: low region below `min elli ellk'`, high region above `max ri rk'`.
  set ellmerge : ℤ := min elli ellk' with hellmergedef
  set rmerge : ℤ := max ri rk' with hrmergedef
  have hbound : ellmerge ≤ rmerge + 1 := by simp only [hellmergedef, hrmergedef]; omega
  set Ulow : Set (ℤ × ℤ) := {z | pi v z < ellmerge} with hUlowdef
  set Uhigh : Set (ℤ × ℤ) := {z | rmerge < pi v z} with hUhighdef
  have hUlowHP : IsHalfPlane Ulow := isHalfPlane_pi_lt hvprim.ne_zero ellmerge
  have hUhighHP : IsHalfPlane Uhigh := isHalfPlane_pi_gt hvprim.ne_zero rmerge
  have hdisjUV : Disjoint Ulow Uhigh := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    simp only [hUlowdef, Set.mem_ofPred_eq] at hz1
    simp only [hUhighdef, Set.mem_ofPred_eq] at hz2
    omega
  set Lmerge : Config (ZMod p) := fun z => Li z + Lk' z with hLmergedef
  set Rmerge : Config (ZMod p) := fun z => Ri z + Rk' z with hRmergedef
  have hLmergedp : DoublyPeriodic Lmerge := doublyPeriodic_add hLidp hLk'dp
  have hRmergedp : DoublyPeriodic Rmerge := doublyPeriodic_add hRidp hRk'dp
  have hsumL : ∀ z ∈ Ulow, (fun z => G i z + G k z) z = Lmerge z := by
    intro z hz
    simp only [hUlowdef, Set.mem_ofPred_eq] at hz
    have h1 : G i z = Li z := hGiL z (by omega)
    have h2 : G k z = Lk' z := hGkL' z (by omega)
    show G i z + G k z = Li z + Lk' z
    rw [h1, h2]
  have hsumR : ∀ z ∈ Uhigh, (fun z => G i z + G k z) z = Rmerge z := by
    intro z hz
    simp only [hUhighdef, Set.mem_ofPred_eq] at hz
    have h1 : G i z = Ri z := hGiR z (by omega)
    have h2 : G k z = Rk' z := hGkR' z (by omega)
    show G i z + G k z = Ri z + Rk' z
    rw [h1, h2]
  have hFPULow : FullyPeriodicOn (fun z => G i z + G k z) Ulow :=
    fullyPeriodicOn_of_eqOn_doublyPeriodic hUlowHP hLmergedp hsumL
  have hFPUHigh : FullyPeriodicOn (fun z => G i z + G k z) Uhigh :=
    fullyPeriodicOn_of_eqOn_doublyPeriodic hUhighHP hRmergedp hsumR
  -- Reindex over `Fin (m - 1)`, replacing the slot of `k` by the merged component and deleting `i`.
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  subst hn
  show AdmissibleDecomp zeta n
  obtain ⟨z0, hz0⟩ := Fin.exists_succAbove_eq hik.symm
  refine ⟨fun j z => if j = z0 then G i z + G k z else G (i.succAbove j) z,
    fun j => if j = z0 then (L : ℤ) • v else h (i.succAbove j),
    fun j => if j = z0 then Ulow else U (i.succAbove j),
    fun j => if j = z0 then Uhigh else V (i.succAbove j),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    have hz := hsum z
    rw [Fin.sum_univ_succAbove (fun l => G l z) i] at hz
    have hpointwise : ∀ j : Fin n,
        (if j = z0 then G i z + G k z else G (i.succAbove j) z) =
          G (i.succAbove j) z + (if j = z0 then G i z else 0) := by
      intro j
      by_cases hj : j = z0
      · simp only [hj, hz0, if_true]; ring
      · simp only [hj, if_false, add_zero]
    rw [Finset.sum_congr rfl (fun j _ => hpointwise j), Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ z0 (fun _ => G i z), if_pos (Finset.mem_univ z0)]
    rw [hz]; abel
  · intro j
    by_cases hj : j = z0
    · simp only [hj, if_true]; exact hLvne
    · simp only [hj, if_false]; exact hne (i.succAbove j)
  · intro j
    by_cases hj : j = z0
    · simp only [hj, if_true]; exact hLvperSum
    · simp only [hj, if_false]; exact hper (i.succAbove j)
  · intro j
    by_cases hj : j = z0
    · simp only [hj, if_true]; exact hUlowHP
    · simp only [hj, if_false]; exact hU (i.succAbove j)
  · intro j
    by_cases hj : j = z0
    · simp only [hj, if_true]; exact hUhighHP
    · simp only [hj, if_false]; exact hV (i.succAbove j)
  · intro j
    by_cases hj : j = z0
    · simp only [hj, if_true]; exact hdisjUV
    · simp only [hj, if_false]; exact hdisj (i.succAbove j)
  · intro j
    by_cases hj : j = z0
    · simp only [hj, if_true]; exact hFPULow
    · simp only [hj, if_false]; exact hUfp (i.succAbove j)
  · intro j
    by_cases hj : j = z0
    · simp only [hj, if_true]; exact hFPUHigh
    · simp only [hj, if_false]; exact hVfp (i.succAbove j)

/-- **Termination.**  Repeating Operations A and C strictly decreases the length, so one reaches
a reduced admissible decomposition; non-periodicity of `ζ` keeps the length at least `2`.
Paper §8.5. -/
theorem exists_reduced_admissibleDecomp {p : ℕ} {zeta : Config (ZMod p)} {m : ℕ}
    (hnper : ¬ IsPeriodic zeta) (hd : AdmissibleDecomp zeta m) :
    ∃ m' : ℕ, 2 ≤ m' ∧ m' ≤ m ∧ ReducedAdmissibleDecomp zeta m' := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    obtain ⟨G, h, U, V, hsum, hne, hper, hU, hV, hdisj, hUfp, hVfp⟩ := hd
    have hm2 : 2 ≤ m :=
      two_le_of_admissibleDecomp hnper ⟨G, h, U, V, hsum, hne, hper, hU, hV, hdisj, hUfp, hVfp⟩
    by_cases hallnd : ∀ i, ¬ DoublyPeriodic (G i)
    · by_cases hallnonpar : Pairwise (fun i j => det (h i) (h j) ≠ 0)
      · -- Already reduced: no component doubly periodic, all periods pairwise non-parallel.
        exact ⟨m, hm2, le_refl m, G, h, U, V, hsum, hne, hper, hallnd, hallnonpar, hU, hV, hdisj,
          hUfp, hVfp⟩
      · -- Some two components have parallel periods: Operation C reduces the length.
        have hex : ∃ i j, i ≠ j ∧ det (h i) (h j) = 0 := by
          by_contra hcon
          push Not at hcon
          exact hallnonpar fun i j hij => hcon i j hij
        obtain ⟨i, j, hij, hpar⟩ := hex
        have hnew : AdmissibleDecomp zeta (m - 1) :=
          exists_admissibleDecomp_of_parallel hm2 hsum hne hper hU hV hdisj hUfp hVfp hallnd hij
            hpar
        obtain ⟨m', hm2', hle', hred'⟩ := ih (m - 1) (by omega) hnew
        exact ⟨m', hm2', by omega, hred'⟩
    · -- Some component is doubly periodic: Operation A absorbs it, reducing the length.
      push Not at hallnd
      obtain ⟨i, hi⟩ := hallnd
      have hnew : AdmissibleDecomp zeta (m - 1) :=
        exists_admissibleDecomp_of_doublyPeriodic_component hm2 hsum hne hper hU hV hdisj hUfp
          hVfp hi
      obtain ⟨m', hm2', hle', hred'⟩ := ih (m - 1) (by omega) hnew
      exact ⟨m', hm2', by omega, hred'⟩

/-! ### Lemma 8.17 -/

/-- A reduced admissible decomposition of a non-periodic `ζ` is literally a star configuration:
Step (α) turns each component into a triple satisfying (S1)–(S3), and reduction supplies (S2)
and the pairwise non-parallelism of the primitive directions. -/
theorem exists_starConfig_of_reduced {p : ℕ} {zeta : Config (ZMod p)} {m : ℕ}
    (hm : 2 ≤ m) (hd : ReducedAdmissibleDecomp zeta m) :
    ∃ S : StarConfig p m, S.θ = zeta := by
  obtain ⟨G, h, U, V, hsum, hne, hper, hnd, hnonpar, hU, hV, hdisj, hUfp, hVfp⟩ := hd
  choose v k L R ell r hvprim hk hvh hkvper hLdp hRdp hellr hGL hGR using
    fun i => exists_strip_of_admissible_component (hne i) (hper i) (hnd i) (hU i) (hV i)
      (hdisj i) (hUfp i) (hVfp i)
  -- Each `h i` is a non-zero multiple of the primitive direction `v i`.
  have hpar : ∀ i, ∃ c : ℤ, c ≠ 0 ∧ h i = c • v i := by
    intro i
    obtain ⟨c, hc⟩ := eq_zsmul_of_det_eq_zero (hvprim i) (hvh i)
    refine ⟨c, fun hc0 => hne i (by rw [hc, hc0, zero_smul]), hc⟩
  choose c hcne hceq using hpar
  -- Transfer pairwise non-parallelism from `h` to `v`.
  have hnonparv : ∀ i j, i ≠ j → det (v i) (v j) ≠ 0 := by
    intro i j hij hcon
    apply hnonpar hij
    rw [hceq i, hceq j, det_zsmul_zsmul, hcon, mul_zero]
  exact ⟨⟨v, G, k, L, R, ell, r, hm, hvprim, hnonparv, hk, hkvper, hnd, hLdp, hRdp, hellr, hGL,
    hGR⟩, funext fun z => (hsum z).symm⟩

/-- **Lemma 8.17 (Normalisation).**  Let `ζ : ℤ² → 𝔽_p` be non-periodic and suppose
`ζ = ∑_{i=1}^m Gᵢ`, where each `Gᵢ` has a non-zero period `hᵢ` and there are disjoint
half-planes `Uᵢ, Vᵢ` on which `Gᵢ` is fully periodic.  Then `ζ` is a star configuration. -/
theorem exists_starConfig_of_admissible {p : ℕ} {zeta : Config (ZMod p)} {m : ℕ}
    (hnper : ¬ IsPeriodic zeta) (hd : AdmissibleDecomp zeta m) :
    ∃ (m' : ℕ) (S : StarConfig p m'), S.θ = zeta := by
  obtain ⟨m', hm', -, hred⟩ := exists_reduced_admissibleDecomp hnper hd
  obtain ⟨S, hS⟩ := exists_starConfig_of_reduced hm' hred
  exact ⟨m', S, hS⟩

/-! ### Theorem 8.1 -/

/-- Corollary 8.10 and Theorem 8.12 together produce an admissible decomposition. -/
theorem FirstHalfPlane.admissibleDecomp {p n : ℕ} [Fact p.Prime] (D : FirstHalfPlane p n)
    (hlow : LowConvexComplexity D.zeta) : AdmissibleDecomp D.zeta n := by
  choose V hVhp hVdisj hVfp using D.exists_second_half_plane hlow
  refine ⟨D.G, D.h, D.U, V, D.sum_eq, D.h_ne_zero, D.h_mem_Per, ?_, hVhp, ?_,
    D.fullyPeriodicOn_U, hVfp⟩
  · exact fun i => isHalfPlane_latHalfPlane (D.primitive i).ne_zero _ _
  · exact fun i => (hVdisj i).symm

/-- **Theorem 8.1 (Structure input).**  Let `ξ` be a counterexample of minimal order.  Then
there are a prime `p` with `A ⊆ [[p]]`, a non-periodic `ζ ∈ X`, an `m ≥ 2` and `𝔽_p`-valued
`G₁, …, G_m` with `ζ = ∑ᵢ Gᵢ` over `𝔽_p`, each `Gᵢ` having a non-zero period `hᵢ`, the `hᵢ`
pairwise non-parallel and no component doubly periodic, such that for every `i`:

(i) `Gᵢ` is fully periodic on a half-plane `Uᵢ` whose boundary is parallel to `hᵢ`;

(ii) `Gᵢ` is fully periodic on a half-plane `Vᵢ` disjoint from `Uᵢ`.

Part (i) is Corollary 8.10, part (ii) is Theorem 8.12. -/
theorem structure_input {ξ : Config ℤ} (hξ : IsMinimalCounterexample ξ) {p : ℕ} [Fact p.Prime]
    (hlt : ∀ z, ξ z < p) :
    ∃ (zeta : Config (ZMod p)) (m : ℕ), ¬ IsPeriodic zeta ∧ 2 ≤ m ∧
      AdmissibleDecomp zeta m ∧ LowConvexComplexity zeta := by
  obtain ⟨n, D, ζ, hζorbit, hζnp, hDzeta⟩ := exists_firstHalfPlane hξ hlt
  obtain ⟨hmin, -⟩ := IsMinimalCounterexample.of_mem_orbitClosure hξ hζorbit hζnp
  obtain ⟨-, hpos, -, hlow⟩ := hmin.1
  -- Values of `ζ` are values of `ξ`, translated: `ζ` also has range in `[[p]]`.
  have hζlt : ∀ z, ζ z < p := by
    intro z
    obtain ⟨u, hu⟩ := hζorbit {z}
    rw [hu z (Finset.mem_singleton_self z)]
    exact hlt _
  obtain ⟨S, hSne, hSconv, hSP⟩ := hlow
  have hlowD : LowConvexComplexity D.zeta := by
    rw [hDzeta]
    exact ⟨S, hSne, hSconv, by rw [P_modP hpos hζlt]; exact hSP⟩
  exact ⟨D.zeta, n, D.zeta_not_periodic, D.two_le, FirstHalfPlane.admissibleDecomp D hlowD, hlowD⟩

end Nivat
