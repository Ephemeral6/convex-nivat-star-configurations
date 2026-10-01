/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Section8.FirstHalfPlane
import Nivat.PeriodCount
import Nivat.SubseqLimit
import Nivat.RayOrder
import Nivat.Section8.SubseqFinite

/-!
# §8.4. The second half-plane

Formalisation of §8.4 of *The Convex Nivat Conjecture* (Pan); this subsection
proves Theorem 8.1(ii), in three steps.

Proposition 8.14 uses **Theorem D.1** (`Nivat.isPeriodic_of_add`) to show that, when `ζ` is
pushed to the limit along a suitable direction, every subsequential limit on the far side of one
component is doubly periodic.  Lemma 8.16 shows that this forces the component to agree with a
doubly periodic field on a half-plane on that side, the point of the argument being that there
are only finitely many such limits.  Lemma 8.15 guarantees that the directions required can
always be found, in a fixed order, so that an induction produces all of the `Vᵢ`.

## Main results

* `Nivat.doublyPeriodic_of_shift_doublyPeriodic` — **Lemma 8.13 (Bi-periodicity over `𝔽_p`)**.
* `Nivat.doublyPeriodic_of_two_component` — the core of **Proposition 8.14**, and the only
  place where Theorem D.1 is used.
* `Nivat.FirstHalfPlane.doublyPeriodic_of_mem_subseqLimits` — **Proposition 8.14**.
* `Nivat.FirstHalfPlane.exists_available_direction` — **Lemma 8.15 (Available directions)**.
* `Nivat.exists_doublyPeriodic_agree` — **Lemma 8.16 (Propagation)**.
* `Nivat.FirstHalfPlane.exists_second_half_plane` — **Theorem 8.12 = Theorem 8.1(ii)**.

## Status

Skeleton; proofs are line D.
-/

namespace Nivat

open Finset

/-! ### Lemma 8.13 -/

/-- **Lemma 8.13 (Bi-periodicity over `𝔽_p`).**  Let `G : ℤ² → 𝔽_p` have a non-zero period `h`,
let `d ∈ ℤ²` be non-parallel to `h`, and suppose `g = (T^d − 1)G` is doubly periodic.  Then `G`
is doubly periodic.

The proof is the telescoping identity `T^{Md} − 1 = (∑_{i<M} T^{id})(T^d − 1)` together with
`(T^{pMd} − 1)G = p ĝ = 0` in characteristic `p`. -/
theorem doublyPeriodic_of_shift_doublyPeriodic {p : ℕ} [Fact p.Prime] {G : Config (ZMod p)}
    {h d : ℤ × ℤ} (hh : h ≠ 0) (hper : h ∈ Per G) (hd : det h d ≠ 0)
    (hg : DoublyPeriodic fun z => G (z + d) - G z) : DoublyPeriodic G := by
  classical
  have _hh_unused := hh
  set g : Config (ZMod p) := fun z => G (z + d) - G z with hgdef
  have hgact : g = act (mono d - 1) G := by
    funext z
    show G (z + d) - G z = act (mono d - 1) G z
    rw [act_sub_left, act_mono, act_one]
    rfl
  -- reduce the period supplied by `hg` to a positive multiple `e = M • d`
  obtain ⟨N, hN, hNmem⟩ := hg.exists_smul_mem
  set M : ℕ := N.natAbs with hMdef
  have hMpos : 0 < M := Int.natAbs_pos.mpr hN
  set e : ℤ × ℤ := (M : ℤ) • d with hedef
  have heper : e ∈ Per g := by
    by_cases hN0 : 0 ≤ N
    · have hMN : (M : ℤ) = N := by rw [hMdef]; exact_mod_cast Int.natAbs_of_nonneg hN0
      rw [hedef, hMN]; exact hNmem d
    · have hN0' : N < 0 := not_le.mp hN0
      have hMN : (M : ℤ) = -N := by rw [hMdef]; omega
      have hee : e = -(N • d) := by rw [hedef, hMN, neg_smul]
      rw [hee]; exact (Per g).neg_mem (hNmem d)
  -- telescoping: `T^{Md} - 1 = (∑_{i<M} T^{id})(T^d - 1)`
  have htel1 : (mono e - 1 : LaurentTwo (ZMod p))
      = (∑ k ∈ Finset.range M, (mono d : LaurentTwo (ZMod p)) ^ k) * (mono d - 1) := by
    rw [hedef, ← mono_pow, geom_sum_mul]
  set g' : Config (ZMod p) := act (mono e - 1) G with hg'def
  have hg'eq : g' = act (∑ k ∈ Finset.range M, (mono d : LaurentTwo (ZMod p)) ^ k) g := by
    rw [hg'def, htel1, act_mul, ← hgact]
  have heper' : e ∈ Per g' := by rw [hg'eq]; exact act_mem_Per heper
  -- `(T^{pMd} - 1)G = p • g' = 0`
  have hfinal : act (mono ((p : ℤ) • e) - 1) G = 0 := by
    have htel2 : (mono ((p : ℤ) • e) - 1 : LaurentTwo (ZMod p))
        = (∑ k ∈ Finset.range p, (mono e : LaurentTwo (ZMod p)) ^ k) * (mono e - 1) := by
      rw [← mono_pow, geom_sum_mul]
    funext z
    rw [htel2, act_mul, ← hg'def, act_sum_apply]
    have hconst : ∀ k ∈ Finset.range p, act (mono e ^ k) g' z = g' z := by
      intro k _
      have hTeq : T ((k : ℤ) • e) g' = g' := (Per g').zsmul_mem heper' k
      rw [mono_pow, act_mono, hTeq]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ZMod.natCast_self, zero_mul]
    rfl
  have hper2 : ((p : ℤ) • e) ∈ Per G := (act_mono_sub_one_eq_zero_iff _ _).mp hfinal
  have hscale : (p : ℤ) • e = ((p : ℤ) * (M : ℤ)) • d := by rw [hedef, smul_smul]
  have hdetne : det h ((p : ℤ) • e) ≠ 0 := by
    rw [hscale]
    have hthis : pi h (((p : ℤ) * (M : ℤ)) • d) = ((p : ℤ) * (M : ℤ)) * pi h d := pi_smul h _ d
    show det h (((p : ℤ) * (M : ℤ)) • d) ≠ 0
    rw [show det h (((p : ℤ) * (M : ℤ)) • d) = ((p : ℤ) * (M : ℤ)) * det h d from hthis]
    have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out (p := p.Prime)).pos.ne'
    have hMne : (M : ℤ) ≠ 0 := by exact_mod_cast hMpos.ne'
    exact mul_ne_zero (mul_ne_zero hpne hMne) hd
  exact ⟨h, hper, (p : ℤ) • e, hper2, hdetne⟩

/-! ### Proposition 8.14 -/

/-- The case analysis at the heart of **Proposition 8.14**, and the only place in §8 where
Theorem D.1 is used.

Let `ζ = ζ₁ + ζ₂` over `𝔽_p` with `ζ₁` of non-zero period `h₁`, `ζ₂` of period `h₂`, the two
non-parallel, and suppose `ζ` has low convex complexity.  Theorem D.1 supplies a non-zero period
`d₀` of `ζ`.  If `d₀ ∥ h₁` then `ζ₂` is doubly periodic; otherwise `ζ₁` is, by Lemma 8.13. -/
theorem doublyPeriodic_left_of_not_parallel {p : ℕ} [Fact p.Prime] {zeta1 zeta2 : Config (ZMod p)}
    {h1 h2 d0 : ℤ × ℤ} (hp1 : h1 ∈ Per zeta1) (hp2 : h2 ∈ Per zeta2) (hh1 : h1 ≠ 0)
    (hindep : det h1 h2 ≠ 0) (hd0 : d0 ∈ Per fun z => zeta1 z + zeta2 z) (hd0ne : d0 ≠ 0)
    (hnpar : det h1 d0 ≠ 0) : DoublyPeriodic zeta1 := by
  classical
  have _hd0ne_unused := hd0ne
  set g : Config (ZMod p) := fun z => zeta1 (z + d0) - zeta1 z with hgdef
  have hgeq : g = fun z => -(zeta2 (z + d0) - zeta2 z) := by
    funext z
    have hkey : zeta1 (z + d0) + zeta2 (z + d0) = zeta1 z + zeta2 z := Per.apply hd0 z
    show zeta1 (z + d0) - zeta1 z = -(zeta2 (z + d0) - zeta2 z)
    linear_combination hkey
  have hh1g : h1 ∈ Per g := by
    rw [mem_Per_iff]
    funext z
    show g (z + h1) = g z
    rw [hgdef]
    show zeta1 (z + h1 + d0) - zeta1 (z + h1) = zeta1 (z + d0) - zeta1 z
    rw [show z + h1 + d0 = z + d0 + h1 from by abel, Per.apply hp1, Per.apply hp1]
  have hh2g : h2 ∈ Per g := by
    rw [mem_Per_iff]
    funext z
    show g (z + h2) = g z
    rw [hgeq]
    show -(zeta2 (z + h2 + d0) - zeta2 (z + h2)) = -(zeta2 (z + d0) - zeta2 z)
    rw [show z + h2 + d0 = z + d0 + h2 from by abel, Per.apply hp2, Per.apply hp2]
  have hgdp : DoublyPeriodic g := ⟨h1, hh1g, h2, hh2g, hindep⟩
  exact doublyPeriodic_of_shift_doublyPeriodic hh1 hp1 hnpar hgdp

/-- If `d₀ ∥ h₁`, take `d₁ ∈ (ℤd₀ ∩ ℤh₁) \ {0}`; then `T^{d₁}ζ₁ = ζ₁` and `T^{d₁}ζ = ζ` give
`T^{d₁}ζ₂ = ζ₂`, and `d₁ ∦ h₂`, so `ζ₂` is doubly periodic.  Paper Proposition 8.14, case (iii). -/
theorem doublyPeriodic_right_of_parallel {p : ℕ} [Fact p.Prime] {zeta1 zeta2 : Config (ZMod p)}
    {h1 h2 d0 : ℤ × ℤ} (hp1 : h1 ∈ Per zeta1) (hp2 : h2 ∈ Per zeta2) (hh1 : h1 ≠ 0)
    (hindep : det h1 h2 ≠ 0) (hd0 : d0 ∈ Per fun z => zeta1 z + zeta2 z) (hd0ne : d0 ≠ 0)
    (hpar : det h1 d0 = 0) : DoublyPeriodic zeta2 := by
  classical
  have hdet : h1.1 * d0.2 - h1.2 * d0.1 = 0 := hpar
  set d1 : ℤ × ℤ := if h1.1 = 0 then h1.2 • d0 else h1.1 • d0 with hd1def
  have hd1eq : d1 = (if h1.1 = 0 then d0.2 else d0.1) • h1 := by
    rw [hd1def]
    split_ifs with hcase
    · apply Prod.ext
      · show h1.2 * d0.1 = d0.2 * h1.1
        linear_combination -hdet
      · show h1.2 * d0.2 = d0.2 * h1.2
        ring
    · apply Prod.ext
      · show h1.1 * d0.1 = d0.1 * h1.1
        ring
      · show h1.1 * d0.2 = d0.1 * h1.2
        linear_combination hdet
  have hd1ne : d1 ≠ 0 := by
    rw [hd1def]
    split_ifs with hcase
    · have hh12 : h1.2 ≠ 0 := fun hcontra => hh1 (Prod.ext hcase hcontra)
      exact smul_ne_zero hh12 hd0ne
    · exact smul_ne_zero hcase hd0ne
  have hd1zeta1 : d1 ∈ Per zeta1 := by
    rw [hd1eq]; exact (Per zeta1).zsmul_mem hp1 _
  have hd1sum : d1 ∈ Per fun z => zeta1 z + zeta2 z := by
    have hex : ∃ c : ℤ, d1 = c • d0 := by
      rw [hd1def]; split_ifs
      · exact ⟨h1.2, rfl⟩
      · exact ⟨h1.1, rfl⟩
    obtain ⟨c, hc⟩ := hex
    rw [hc]; exact (Per _).zsmul_mem hd0 _
  have hzeta2per : d1 ∈ Per zeta2 := by
    rw [mem_Per_iff]
    funext z
    have hsum : zeta1 (z + d1) + zeta2 (z + d1) = zeta1 z + zeta2 z := Per.apply hd1sum z
    have hz1 : zeta1 (z + d1) = zeta1 z := Per.apply hd1zeta1 z
    show zeta2 (z + d1) = zeta2 z
    rw [hz1] at hsum
    exact add_left_cancel hsum
  have hc'ne : (if h1.1 = 0 then d0.2 else d0.1) ≠ 0 := by
    intro hc0
    apply hd1ne
    rw [hd1eq, hc0, zero_smul]
  have hdetne : det d1 h2 ≠ 0 := by
    rw [hd1eq]
    show (if h1.1 = 0 then d0.2 else d0.1) * h1.1 * h2.2 -
        (if h1.1 = 0 then d0.2 else d0.1) * h1.2 * h2.1 ≠ 0
    have heq : (if h1.1 = 0 then d0.2 else d0.1) * h1.1 * h2.2 -
        (if h1.1 = 0 then d0.2 else d0.1) * h1.2 * h2.1
        = (if h1.1 = 0 then d0.2 else d0.1) * (h1.1 * h2.2 - h1.2 * h2.1) := by ring
    rw [heq]
    exact mul_ne_zero hc'ne hindep
  exact ⟨d1, hzeta2per, h2, hp2, hdetne⟩

/-- **Proposition 8.14**, core form.  A two-component configuration of low convex complexity
whose first component is not doubly periodic has a doubly periodic second component.

This is where the reduction of §8 meets Appendix D: `Nivat.isPeriodic_of_add` is Theorem D.1. -/
theorem doublyPeriodic_of_two_component {p : ℕ} [Fact p.Prime] {zeta1 zeta2 : Config (ZMod p)}
    {h1 h2 : ℤ × ℤ} (hp1 : h1 ∈ Per zeta1) (hp2 : h2 ∈ Per zeta2) (hh1 : h1 ≠ 0)
    (hindep : det h1 h2 ≠ 0) {S : Finset (ℤ × ℤ)} (hne : S.Nonempty) (hS : LatticeConvex S)
    (hP : P (fun z => zeta1 z + zeta2 z) S ≤ S.card) (hnd : ¬ DoublyPeriodic zeta1) :
    DoublyPeriodic zeta2 := by
  -- Theorem D.1 supplies a non-zero period `d₀` of `ζ = ζ₁ + ζ₂`.
  obtain ⟨d0, hd0, hd0ne⟩ := isPeriodic_of_add hp1 hp2 hh1 hindep hne hS hP
  by_cases hpar : det h1 d0 = 0
  · exact doublyPeriodic_right_of_parallel hp1 hp2 hh1 hindep hd0 hd0ne hpar
  · exact absurd (doublyPeriodic_left_of_not_parallel hp1 hp2 hh1 hindep hd0 hd0ne hpar) hnd

/-! ### Safe directions -/

/-- `d` is *safe* for `G` if the translates `T^{nd}G` converge pointwise to a doubly periodic
field, the convergence being eventual equality at each point.  Paper §8.4, "safe directions":
this happens as soon as `G` is fully periodic on a half-plane `H` into which `d` points, the
limit being the global extension `G^H` of Lemma 8.2. -/
def SafeFor {p : ℕ} (G : Config (ZMod p)) (d : ℤ × ℤ) : Prop :=
  ∃ G' : Config (ZMod p), DoublyPeriodic G' ∧
    ∀ z : ℤ × ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → G (z + (n : ℤ) • d) = G' z

/-- `piE` is additive in its argument. -/
private theorem piE_add (ε : Bool) (v z w : ℤ × ℤ) :
    piE ε v (z + w) = piE ε v z + piE ε v w := by
  cases ε with
  | true => exact pi_add v z w
  | false => show -pi v (z + w) = -pi v z + -pi v w; rw [pi_add]; ring

/-- `piE` scales linearly under integer scalar multiples. -/
private theorem piE_zsmul (ε : Bool) (v : ℤ × ℤ) (c : ℤ) (z : ℤ × ℤ) :
    piE ε v (c • z) = c * piE ε v z := by
  cases ε with
  | true => exact pi_smul v c z
  | false => show -pi v (c • z) = c * -pi v z; rw [pi_smul]; ring

/-- A direction pointing into a half-plane of full periodicity, along which the doubly periodic
global extension of `G|_H` already agrees with `d`'s own period lattice, is safe.  Paper §8.4,
"Safe directions": the paper fixes an `N` divisible by all the relevant `kⱼ` with `Nℤ²` inside
the period lattice of every `G_j^H` produced so far, and calls `d ∈ Nℤ²` "safe for `j`" if it
points into some `H ∈ 𝒦ⱼ`; the hypothesis `hdper : d ∈ Per G'` records exactly `d ∈ Nℤ² ⊆ Per G'`
for the particular `H = latHalfPlane ε v t` and `G' = G_j^H` in play. -/
theorem safeFor_of_fullyPeriodic {p : ℕ} {G : Config (ZMod p)} {v : ℤ × ℤ} {ε : Bool} {t : ℤ}
    (hfp : FullyPeriodicOn G (latHalfPlane ε v t))
    {G' : Config (ZMod p)} (hG'dp : DoublyPeriodic G')
    (hext : ∀ z ∈ latHalfPlane ε v t, G' z = G z)
    {d : ℤ × ℤ} (hd : 0 < piE ε v d) (hdper : d ∈ Per G') :
    SafeFor G d := by
  have _hfp_unused := hfp
  refine ⟨G', hG'dp, fun z => ?_⟩
  set N₀ : ℕ := (t - piE ε v z).toNat with hN₀def
  refine ⟨N₀, fun n hn => ?_⟩
  have hmem : z + (n : ℤ) • d ∈ latHalfPlane ε v t := by
    show t ≤ piE ε v (z + (n : ℤ) • d)
    rw [piE_add, piE_zsmul]
    have h1 : (1 : ℤ) ≤ piE ε v d := hd
    have h2 : (n : ℤ) ≤ (n : ℤ) * piE ε v d := by
      calc (n : ℤ) = (n : ℤ) * 1 := (mul_one _).symm
      _ ≤ (n : ℤ) * piE ε v d := mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (t - piE ε v z : ℤ) ≤ (n : ℤ) :=
      le_trans (Int.self_le_toNat _) (by exact_mod_cast hn)
    linarith
  have hperz : ((n : ℤ) • d) ∈ Per G' := (Per G').zsmul_mem hdper n
  have hGper : G' (z + (n : ℤ) • d) = G' z := Per.apply hperz z
  rw [← hext _ hmem, hGper]

/-- A safe direction forces the subsequential limits to be the single doubly periodic field
`G^H`.  Paper §8.4. -/
theorem subseqLimits_of_safeFor {p : ℕ} {G : Config (ZMod p)} {d : ℤ × ℤ} (h : SafeFor G d) :
    ∃ G' : Config (ZMod p), DoublyPeriodic G' ∧ subseqLimits G d = {G'} := by
  classical
  obtain ⟨G', hdp, hev⟩ := h
  choose Nf hNf using hev
  refine ⟨G', hdp, ?_⟩
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨fun W M => ?_, fun y hy => ?_⟩
  · refine ⟨max M (W.sup Nf), le_max_left _ _, fun w hw => ?_⟩
    have hNw : Nf w ≤ max M (W.sup Nf) := le_trans (Finset.le_sup hw) (le_max_right _ _)
    exact (hNf w _ hNw).symm
  · funext z
    obtain ⟨n, hnN, hn⟩ := hy {z} (Nf z)
    have hz : y z = G (z + (n : ℤ) • d) := hn z (by simp)
    rw [hz]
    exact hNf z n hnN

/-- Every rational half-plane through a primitive `v` is non-empty: `π v` is surjective, so
some lattice point achieves any prescribed value of `π_ε v`. -/
private theorem latHalfPlane_nonempty {v : ℤ × ℤ} (hv : Primitive v) (ε : Bool) (t : ℤ) :
    (latHalfPlane ε v t).Nonempty := by
  cases ε with
  | true =>
    obtain ⟨z, hz⟩ := pi_surjective hv t
    exact ⟨z, hz.ge⟩
  | false =>
    obtain ⟨z, hz⟩ := pi_surjective hv (-t)
    refine ⟨z, ?_⟩
    show t ≤ -pi v z
    omega

/-- Given a finite set of pairwise doubly periodic configurations, there is a single non-zero
scale `N` such that `N • w` is a period of every configuration in the set, for every `w`.  This
is the "finite intersection of period lattices contains `N ℤ²`" step of Lemma 8.16, Step 2,
obtained directly (without any index theory) by multiplying together one witness per element of
the finite set. -/
private theorem exists_common_smul_mem_Per {p : ℕ} {Ω : Set (Config (ZMod p))} (hΩfin : Ω.Finite)
    (hΩdp : ∀ y ∈ Ω, DoublyPeriodic y) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ y ∈ Ω, ∀ w : ℤ × ℤ, N • w ∈ Per y := by
  classical
  set ΩF : Finset (Config (ZMod p)) := hΩfin.toFinset with hΩFdef
  set Nfun : Config (ZMod p) → ℤ := fun y =>
    if h : DoublyPeriodic y then h.exists_smul_mem.choose else 1 with hNfundef
  have hNfunne : ∀ y, DoublyPeriodic y → Nfun y ≠ 0 := by
    intro y hy
    rw [hNfundef]; simp only [dif_pos hy]
    exact hy.exists_smul_mem.choose_spec.1
  have hNfunmem : ∀ y, DoublyPeriodic y → ∀ w, Nfun y • w ∈ Per y := by
    intro y hy w
    rw [hNfundef]; simp only [dif_pos hy]
    exact hy.exists_smul_mem.choose_spec.2 w
  refine ⟨∏ y ∈ ΩF, Nfun y, ?_, ?_⟩
  · apply Finset.prod_ne_zero_iff.mpr
    intro y hy
    have hyΩ : y ∈ Ω := by rwa [hΩFdef, Set.Finite.mem_toFinset] at hy
    exact hNfunne y (hΩdp y hyΩ)
  · intro y hy w
    have hyF : y ∈ ΩF := by rwa [hΩFdef, Set.Finite.mem_toFinset]
    have hsplit : (∏ y' ∈ ΩF, Nfun y') = Nfun y * ∏ y' ∈ ΩF.erase y, Nfun y' :=
      (Finset.mul_prod_erase ΩF Nfun hyF).symm
    rw [hsplit, mul_smul]
    exact hNfunmem y (hΩdp y hy) _

/-- The positive version of `exists_common_smul_mem_Per`: since `Per y` is closed under
negation, the common scalar `N` may be replaced by `|N|` without disturbing membership. -/
private theorem exists_common_smul_mem_Per_pos {p : ℕ} {Ω : Set (Config (ZMod p))}
    (hΩfin : Ω.Finite) (hΩdp : ∀ y ∈ Ω, DoublyPeriodic y) :
    ∃ N : ℕ, 0 < N ∧ ∀ y ∈ Ω, ∀ w : ℤ × ℤ, (N : ℤ) • w ∈ Per y := by
  obtain ⟨N, hN, hNmem⟩ := exists_common_smul_mem_Per hΩfin hΩdp
  refine ⟨N.natAbs, Int.natAbs_pos.mpr hN, fun y hy w => ?_⟩
  by_cases hN0 : 0 ≤ N
  · have hMN : (N.natAbs : ℤ) = N := by omega
    rw [hMN]; exact hNmem y hy w
  · have hMN : (N.natAbs : ℤ) = -N := by omega
    rw [hMN, neg_smul]
    exact (Per y).neg_mem (hNmem y hy w)

/-! ### Normalisation helper lemmas (for `exists_normalised`) -/

private theorem det_neg_left (a b : ℤ × ℤ) : det (-a) b = -det a b := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

private theorem det_neg_right (a b : ℤ × ℤ) : det a (-b) = -det a b := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

private theorem det_ite_ne_zero (ε1 ε2 : Bool) {a b : ℤ × ℤ} (hab : det a b ≠ 0) :
    det (if ε1 then a else -a) (if ε2 then b else -b) ≠ 0 := by
  split_ifs with h1 h2
  · exact hab
  · rw [det_neg_right]; exact neg_ne_zero.mpr hab
  · rw [det_neg_left]; exact neg_ne_zero.mpr hab
  · rw [det_neg_left, det_neg_right, neg_neg]; exact hab

private theorem primitive_neg {v : ℤ × ℤ} (hv : Primitive v) : Primitive (-v) := by
  show IsCoprime (-v).1 (-v).2
  rw [Prod.fst_neg, Prod.snd_neg]
  exact hv.neg_left.neg_right

private theorem primitive_ite (ε : Bool) {v : ℤ × ℤ} (hv : Primitive v) :
    Primitive (if ε then v else -v) := by
  cases ε
  · simpa using primitive_neg hv
  · simpa using hv

private theorem zsmul_ite (ε : Bool) (k : ℤ) (v : ℤ × ℤ) :
    k • (if ε then v else -v) = if ε then k • v else -(k • v) := by
  cases ε <;> simp [smul_neg]

private theorem pi_neg (v z : ℤ × ℤ) : pi (-v) z = -pi v z := by
  simp only [pi, det, Prod.fst_neg, Prod.snd_neg]; ring

private theorem piE_true_ite (ε : Bool) (v z : ℤ × ℤ) :
    piE true (if ε then v else -v) z = piE ε v z := by
  cases ε with
  | true => rfl
  | false => show pi (-v) z = -pi v z; exact pi_neg v z

private theorem latHalfPlane_ite (ε : Bool) (v : ℤ × ℤ) (t : ℤ) :
    latHalfPlane true (if ε then v else -v) t = latHalfPlane ε v t := by
  ext z
  simp only [latHalfPlane, Set.mem_ofPred_eq, piE_true_ite]

private theorem piR_neg (v : ℤ × ℤ) (y : ℝ × ℝ) : piR (-v) y = -piR v y := by
  simp only [piR, Prod.fst_neg, Prod.snd_neg, Int.cast_neg]; ring

private theorem piER_true_ite (ε : Bool) (v : ℤ × ℤ) (y : ℝ × ℝ) :
    piER true (if ε then v else -v) y = piER ε v y := by
  cases ε with
  | true => rfl
  | false => show piR (-v) y = -piR v y; exact piR_neg v y

private theorem toReal_neg (v : ℤ × ℤ) : toReal (-v) = -toReal v := by
  simp [toReal, Prod.fst_neg, Prod.snd_neg]

private theorem lineR_neg (v : ℤ × ℤ) : lineR (-v) = lineR v := by
  ext y
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨-c, by rw [hc, toReal_neg]; module⟩
  · rintro ⟨c, hc⟩
    exact ⟨-c, by rw [hc, toReal_neg]; module⟩

private theorem lineR_ite (ε : Bool) (v : ℤ × ℤ) :
    lineR (if ε then v else -v) = lineR v := by
  cases ε
  · simpa using lineR_neg v
  · simp

/-! ### Helper lemmas for `doublyPeriodic_of_mem_subseqLimits` -/

/-- A common period of two configurations is a period of their sum (reproduced privately here;
the version in `Nivat.Section8.Normalisation` is `private` there). -/
private theorem per_add_mem' {p : ℕ} {f g : Config (ZMod p)} {u : ℤ × ℤ}
    (hf : u ∈ Per f) (hg : u ∈ Per g) : u ∈ Per (fun z => f z + g z) := by
  rw [mem_Per_iff]
  funext z
  show f (z + u) + g (z + u) = f z + g z
  rw [Per.apply hf z, Per.apply hg z]

/-- A common period of two configurations is a period of their difference. -/
private theorem per_sub_mem' {p : ℕ} {f g : Config (ZMod p)} {u : ℤ × ℤ}
    (hf : u ∈ Per f) (hg : u ∈ Per g) : u ∈ Per (fun z => f z - g z) := by
  rw [mem_Per_iff]
  funext z
  show f (z + u) - g (z + u) = f z - g z
  rw [Per.apply hf z, Per.apply hg z]

/-- The zero configuration is doubly periodic. -/
private theorem doublyPeriodic_zero {p : ℕ} : DoublyPeriodic (fun _ : ℤ × ℤ => (0 : ZMod p)) := by
  refine ⟨(1, 0), ?_, (0, 1), ?_, ?_⟩
  · rw [mem_Per_iff]; funext z; rfl
  · rw [mem_Per_iff]; funext z; rfl
  · simp [det]

/-- The sum of two doubly periodic configurations is doubly periodic: scale a period of each by
the other's period-index to get a common pair of independent periods for the sum. -/
private theorem doublyPeriodic_add {p : ℕ} {f g : Config (ZMod p)} (hf : DoublyPeriodic f)
    (hg : DoublyPeriodic g) : DoublyPeriodic (fun z => f z + g z) := by
  obtain ⟨N1, hN1, hN1mem⟩ := hf.exists_smul_mem
  obtain ⟨N2, hN2, hN2mem⟩ := hg.exists_smul_mem
  have hf1 : (N1 * N2) • ((1, 0) : ℤ × ℤ) ∈ Per f := by rw [mul_smul]; exact hN1mem _
  have hg1 : (N1 * N2) • ((1, 0) : ℤ × ℤ) ∈ Per g := by
    rw [mul_comm N1 N2, mul_smul]; exact hN2mem _
  have hf2 : (N1 * N2) • ((0, 1) : ℤ × ℤ) ∈ Per f := by rw [mul_smul]; exact hN1mem _
  have hg2 : (N1 * N2) • ((0, 1) : ℤ × ℤ) ∈ Per g := by
    rw [mul_comm N1 N2, mul_smul]; exact hN2mem _
  refine ⟨(N1 * N2) • ((1, 0) : ℤ × ℤ), per_add_mem' hf1 hg1,
    (N1 * N2) • ((0, 1) : ℤ × ℤ), per_add_mem' hf2 hg2, ?_⟩
  rw [det_zsmul_zsmul]
  have hdet : det ((1, 0) : ℤ × ℤ) ((0, 1) : ℤ × ℤ) = 1 := by simp [det]
  rw [hdet, mul_one]
  exact mul_ne_zero (mul_ne_zero hN1 hN2) (mul_ne_zero hN1 hN2)

/-- If `f + g` and `g` are both doubly periodic, so is `f`. -/
private theorem doublyPeriodic_of_add_doublyPeriodic {p : ℕ} {f g : Config (ZMod p)}
    (hfg : DoublyPeriodic fun z => f z + g z) (hg : DoublyPeriodic g) : DoublyPeriodic f := by
  obtain ⟨N1, hN1, hN1mem⟩ := hfg.exists_smul_mem
  obtain ⟨N2, hN2, hN2mem⟩ := hg.exists_smul_mem
  have hfg1 : (N1 * N2) • ((1, 0) : ℤ × ℤ) ∈ Per fun z => f z + g z := by
    rw [mul_smul]; exact hN1mem _
  have hg1 : (N1 * N2) • ((1, 0) : ℤ × ℤ) ∈ Per g := by
    rw [mul_comm N1 N2, mul_smul]; exact hN2mem _
  have hfg2 : (N1 * N2) • ((0, 1) : ℤ × ℤ) ∈ Per fun z => f z + g z := by
    rw [mul_smul]; exact hN1mem _
  have hg2 : (N1 * N2) • ((0, 1) : ℤ × ℤ) ∈ Per g := by
    rw [mul_comm N1 N2, mul_smul]; exact hN2mem _
  have heq : (fun z => (f z + g z) - g z) = f := by funext z; ring
  have hf1 : (N1 * N2) • ((1, 0) : ℤ × ℤ) ∈ Per f := by
    have := per_sub_mem' hfg1 hg1; rwa [heq] at this
  have hf2 : (N1 * N2) • ((0, 1) : ℤ × ℤ) ∈ Per f := by
    have := per_sub_mem' hfg2 hg2; rwa [heq] at this
  refine ⟨(N1 * N2) • ((1, 0) : ℤ × ℤ), hf1, (N1 * N2) • ((0, 1) : ℤ × ℤ), hf2, ?_⟩
  rw [det_zsmul_zsmul]
  have hdet : det ((1, 0) : ℤ × ℤ) ((0, 1) : ℤ × ℤ) = 1 := by simp [det]
  rw [hdet, mul_one]
  exact mul_ne_zero (mul_ne_zero hN1 hN2) (mul_ne_zero hN1 hN2)

/-- A finite sum of doubly periodic configurations is doubly periodic. -/
private theorem doublyPeriodic_sum {p : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Config (ZMod p))
    (hf : ∀ i ∈ s, DoublyPeriodic (f i)) : DoublyPeriodic (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact doublyPeriodic_zero
  | insert a s' ha ih =>
    have hfa : DoublyPeriodic (f a) := hf a (Finset.mem_insert_self a s')
    have hrest : ∀ i ∈ s', DoublyPeriodic (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hsum' : DoublyPeriodic (fun z => ∑ i ∈ s', f i z) := ih hrest
    have heq : (fun z => ∑ i ∈ insert a s', f i z) = (fun z => f a z + ∑ i ∈ s', f i z) := by
      funext z; rw [Finset.sum_insert ha]
    rw [heq]
    exact doublyPeriodic_add hfa hsum'

namespace FirstHalfPlane

variable {p n : ℕ} (D : FirstHalfPlane p n)

/-- After the normalisation of §8.4 — replacing `(vⱼ, uⱼ, hⱼ)` by `(−vⱼ, −uⱼ, −hⱼ)` whenever
`εⱼ = −` — one may assume `εⱼ = +` throughout, that is `Uⱼ = {πⱼ ≥ tⱼ}`. -/
def Normalised : Prop := ∀ i, D.eps i = true

/-- The normalisation of §8.4 is always available: replace `vᵢ` by `−vᵢ` whenever `εᵢ = −`, and
`εᵢ` by `+` throughout.  All of the structure fields transport along `piE true (±v) = piE ε v`,
`det`/`Primitive`/`lineR` under sign changes, and `Per`'s closure under negation.  The components
`G` and the sets `U i` are literally unchanged, which lets `exists_second_half_plane` reduce to
the normalised case and transport the answer back for free. -/
theorem exists_normalised : ∃ D' : FirstHalfPlane p n, D'.Normalised ∧ D'.zeta = D.zeta ∧
    D'.G = D.G ∧ ∀ i, D'.U i = D.U i := by
  classical
  refine ⟨{
    zeta := D.zeta
    G := D.G
    v := fun i => if D.eps i then D.v i else -(D.v i)
    k := D.k
    eps := fun _ => true
    t := D.t
    K := D.K
    two_le := D.two_le
    primitive := fun i => primitive_ite (D.eps i) (D.primitive i)
    k_pos := D.k_pos
    nonparallel := by
      intro i j hij
      exact det_ite_ne_zero (D.eps i) (D.eps j) (D.nonparallel hij)
    sum_eq := D.sum_eq
    period := fun i => by
      show ((D.k i : ℤ) • (if D.eps i then D.v i else -(D.v i))) ∈ Per (D.G i)
      rw [zsmul_ite]
      split_ifs with h
      · exact D.period i
      · exact (Per (D.G i)).neg_mem (D.period i)
    not_doublyPeriodic := D.not_doublyPeriodic
    zeta_not_periodic := D.zeta_not_periodic
    fullyPeriodic_U := fun i => by
      show FullyPeriodicOn (D.G i)
        (latHalfPlane true (if D.eps i then D.v i else -(D.v i)) (D.t i))
      rw [latHalfPlane_ite]
      exact D.fullyPeriodic_U i
    K_sector := D.K_sector
    K_side := fun i y hy => by
      show 0 ≤ piER true (if D.eps i then D.v i else -(D.v i)) y
      rw [piER_true_ite]
      exact D.K_side i y hy
    K_interior := fun i => by
      show ¬ (lineR (if D.eps i then D.v i else -(D.v i)) ∩ interior D.K).Nonempty
      rw [lineR_ite]
      exact D.K_interior i
  }, fun _ => rfl, rfl, rfl, fun i => by
    show latHalfPlane true (if D.eps i then D.v i else -(D.v i)) (D.t i) = D.U i
    rw [latHalfPlane_ite]; rfl⟩

/-- `d` *fixes* `j`: `d ∥ hⱼ`, and then `T^d Gⱼ = Gⱼ`.  Paper §8.4. -/
def Fixes (d : ℤ × ℤ) (j : Fin n) : Prop := det (D.v j) d = 0 ∧ d ∈ Per (D.G j)

/-- **Proposition 8.14 (Two-component limits).**  Let `b ≠ c`, let `d` fix `c`, let
`π_b(d) < 0` and let `d` be safe for every `j ∉ {b, c}`.  Then every subsequential limit of
`(T^{nd}G_b)` is doubly periodic.

Indeed `T^{nd}ζ → ζ' = G_c + B + Ĝ_b` pointwise with `B = ∑_{j ≠ b,c} G_j^{H_j}` doubly
periodic; `ζ'` lies in the orbit closure, so it has low convex complexity, and `G_c + B` is not
doubly periodic (else `G_c` would be, contradicting Corollary 8.10).  Now apply
`Nivat.doublyPeriodic_of_two_component`. -/
theorem doublyPeriodic_of_mem_subseqLimits [Fact p.Prime] (hlow : LowConvexComplexity D.zeta)
    {b c : Fin n} (hbc : b ≠ c) {d : ℤ × ℤ} (hd : d ≠ 0) (hfix : D.Fixes d c)
    (hneg : piE (D.eps b) (D.v b) d < 0)
    (hsafe : ∀ j, j ≠ b → j ≠ c → SafeFor (D.G j) d)
    {Gb : Config (ZMod p)} (hGb : Gb ∈ subseqLimits (D.G b) d) : DoublyPeriodic Gb := by
  classical
  have _hd_unused := hd
  have _hneg_unused := hneg
  obtain ⟨hfix1, hfix2⟩ := hfix
  have _hfix1_unused := hfix1
  -- choose doubly periodic limits for the safe components `j ∉ {b, c}`
  have hsafe'' : ∀ j : Fin n, ∃ Gj' : Config (ZMod p),
      (j ≠ b ∧ j ≠ c → DoublyPeriodic Gj' ∧
        ∀ z, ∃ N : ℕ, ∀ s : ℕ, N ≤ s → D.G j (z + (s : ℤ) • d) = Gj' z) := by
    intro j
    by_cases hj : j ≠ b ∧ j ≠ c
    · obtain ⟨Gj', hdp, hev⟩ := hsafe j hj.1 hj.2
      exact ⟨Gj', fun _ => ⟨hdp, hev⟩⟩
    · exact ⟨fun _ => 0, fun hcon => absurd hcon hj⟩
  choose Gind hind using hsafe''
  set OC : Finset (Fin n) := Finset.univ.filter (fun j => j ≠ b ∧ j ≠ c) with hOCdef
  set B : Config (ZMod p) := fun z => ∑ j ∈ OC, Gind j z with hBdef
  have hdpB : DoublyPeriodic B := by
    rw [hBdef]
    exact doublyPeriodic_sum OC Gind (fun j hj => (hind j (Finset.mem_filter.mp hj).2).1)
  set Nfun : Fin n → (ℤ × ℤ) → ℕ := fun j z =>
    if h : j ≠ b ∧ j ≠ c then ((hind j h).2 z).choose else 0 with hNfundef
  have hNfun' : ∀ j (h : j ≠ b ∧ j ≠ c) (z : ℤ × ℤ) (s : ℕ), Nfun j z ≤ s →
      D.G j (z + (s : ℤ) • d) = Gind j z := by
    intro j h z s hs
    have heq : Nfun j z = ((hind j h).2 z).choose := by rw [hNfundef]; simp only [dif_pos h]
    rw [heq] at hs
    exact ((hind j h).2 z).choose_spec s hs
  -- `ζ_c` is exactly periodic under `d`
  have hGc_per : ∀ (z : ℤ × ℤ) (s : ℕ), D.G c (z + (s : ℤ) • d) = D.G c z := fun z s =>
    Per.apply ((Per (D.G c)).zsmul_mem hfix2 s) z
  set zeta1 : Config (ZMod p) := fun z => D.G c z + B z with hz1def
  -- split `∑ᵢ` over `Fin n` into `{b}`, `{c}`, `OC`
  have hOCbc : ({b, c} : Finset (Fin n)) ∪ OC = Finset.univ := by
    ext j
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, hOCdef,
      Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    by_cases hjb : j = b
    · exact Or.inl (Or.inl hjb)
    · by_cases hjc : j = c
      · exact Or.inl (Or.inr hjc)
      · exact Or.inr ⟨hjb, hjc⟩
  have hdisj : Disjoint ({b, c} : Finset (Fin n)) OC := by
    rw [Finset.disjoint_left]
    intro j hj hjOC
    rw [hOCdef, Finset.mem_filter] at hjOC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with h | h
    · exact hjOC.2.1 h
    · exact hjOC.2.2 h
  have hbc' : b ∉ ({c} : Finset (Fin n)) := by simpa using hbc
  have hsplit : ∀ z : ℤ × ℤ, ∑ i, D.G i z = D.G b z + D.G c z + ∑ j ∈ OC, D.G j z := by
    intro z
    rw [← hOCbc, Finset.sum_union hdisj, Finset.sum_insert hbc', Finset.sum_singleton]
  -- `ζ' := G_b + ζ1` lies in `subseqLimits D.zeta d`
  have hmemsub : (fun z => Gb z + zeta1 z) ∈ subseqLimits D.zeta d := by
    intro W M
    have hMtot_ex : ∃ Mtot : ℕ, M ≤ Mtot ∧
        ∀ w ∈ W, ∀ j, j ≠ b → j ≠ c → Nfun j w ≤ Mtot := by
      set Msup : ℕ := (W ×ˢ (Finset.univ : Finset (Fin n))).sup (fun q => Nfun q.2 q.1)
        with hMsupdef
      refine ⟨M ⊔ Msup, le_sup_left, fun w hw j hjb hjc => ?_⟩
      have hmem : (w, j) ∈ W ×ˢ (Finset.univ : Finset (Fin n)) :=
        Finset.mem_product.mpr ⟨hw, Finset.mem_univ j⟩
      have hle : Nfun j w ≤ Msup := by
        rw [hMsupdef]
        exact Finset.le_sup (f := fun q : (ℤ × ℤ) × Fin n => Nfun q.2 q.1) hmem
      exact le_trans hle le_sup_right
    obtain ⟨Mtot, hMMtot, hMtot⟩ := hMtot_ex
    obtain ⟨s, hMtots, hGbeq⟩ := hGb W Mtot
    refine ⟨s, le_trans hMMtot hMtots, fun w hw => ?_⟩
    show Gb w + zeta1 w = D.zeta (w + (s : ℤ) • d)
    have hzeta : D.zeta (w + (s : ℤ) • d) = ∑ i, D.G i (w + (s : ℤ) • d) := D.sum_eq _
    rw [hzeta, hsplit]
    have hb : D.G b (w + (s : ℤ) • d) = Gb w := (hGbeq w hw).symm
    have hc : D.G c (w + (s : ℤ) • d) = D.G c w := hGc_per w s
    have hOCeq : ∑ j ∈ OC, D.G j (w + (s : ℤ) • d) = ∑ j ∈ OC, Gind j w := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjne := (Finset.mem_filter.mp hj).2
      exact hNfun' j hjne w s (le_trans (hMtot w hw j hjne.1 hjne.2) hMtots)
    rw [hb, hc, hOCeq]
    show Gb w + (D.G c w + B w) = Gb w + D.G c w + ∑ j ∈ OC, Gind j w
    rw [hBdef]; ring
  have hmemoc : (fun z => Gb z + zeta1 z) ∈ orbitClosure D.zeta :=
    subseqLimits_subset_orbitClosure D.zeta d hmemsub
  have _hlow_unused := hlow
  have _hmemoc_unused := hmemoc
  -- case split: is `ζ1 = G_c + B` doubly periodic?
  by_cases hzeta1dp : DoublyPeriodic zeta1
  · -- then `G_c = ζ1 - B` would be doubly periodic, contradicting Corollary 8.10
    exact absurd
      (doublyPeriodic_of_add_doublyPeriodic (f := D.G c) (g := B) (by rwa [hz1def] at hzeta1dp)
        hdpB)
      (D.not_doublyPeriodic c)
  · -- otherwise apply `doublyPeriodic_of_two_component` with `zeta1 := ζ1`, `zeta2 := Gb`,
    -- periods `h1 := Nb • D.h c` (a common period of `G_c` and `B`, hence of `ζ1`) and
    -- `h2 := D.h b` (a period of `Gb`, transferred from `D.h b ∈ Per (D.G b)` along the limit).
    obtain ⟨S, hSne, hSlc, hSP⟩ := hlow
    have hSfin : (patterns D.zeta S).Finite := patterns_finite D.zeta S
    have hPle : P (fun z => Gb z + zeta1 z) S ≤ S.card :=
      le_trans (P_le_of_mem_orbitClosure hmemoc S hSfin) hSP
    have hfeq : (fun z => zeta1 z + Gb z) = (fun z => Gb z + zeta1 z) := by
      funext z; ring
    have hPle' : P (fun z => zeta1 z + Gb z) S ≤ S.card := by rw [hfeq]; exact hPle
    obtain ⟨Nb, hNb, hNbmem⟩ := hdpB.exists_smul_mem
    have h1mem : (Nb • D.h c) ∈ Per zeta1 :=
      per_add_mem' ((Per (D.G c)).zsmul_mem (D.h_mem_Per c) Nb) (hNbmem (D.h c))
    have h1ne : (Nb • D.h c) ≠ 0 := smul_ne_zero hNb (D.h_ne_zero c)
    have h2mem : D.h b ∈ Per Gb := mem_Per_of_mem_subseqLimits hGb (D.h_mem_Per b)
    have hdetne : det (Nb • D.h c) (D.h b) ≠ 0 := by
      have heq1 : Nb • D.h c = (Nb * (D.k c : ℤ)) • D.v c := by
        show Nb • ((D.k c : ℤ) • D.v c) = (Nb * (D.k c : ℤ)) • D.v c
        rw [smul_smul]
      have heq2 : D.h b = (D.k b : ℤ) • D.v b := rfl
      rw [heq1, heq2, det_zsmul_zsmul]
      have hkc : (D.k c : ℤ) ≠ 0 := by exact_mod_cast (D.k_pos c).ne'
      have hkb : (D.k b : ℤ) ≠ 0 := by exact_mod_cast (D.k_pos b).ne'
      have hvcb : det (D.v c) (D.v b) ≠ 0 := D.nonparallel hbc.symm
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero hNb hkc) hkb) hvcb
    exact doublyPeriodic_of_two_component h1mem h2mem h1ne hdetne hSne hSlc hPle' hzeta1dp

/-- **Lemma 8.15 (Available directions).**  Let `O` be the set of components for which no `Vⱼ`
has yet been produced, `O ≠ ∅`.  Then there are `b ∈ O`, `c ≠ b` and `d` satisfying all the
hypotheses of Proposition 8.14.

The proof intersects the half-planes `{πⱼ ≥ 0}` for `j ∈ O` into a closed sector `K_O ⊆ K_R` of
opening `< π`, and takes for `rc` the first of the rays `±vⱼ` met when turning anticlockwise
from one of its boundary rays. -/
theorem exists_available_direction (hnorm : D.Normalised) (V : Fin n → Set (ℤ × ℤ))
    (O : Finset (Fin n)) (hO : O.Nonempty)
    (hV : ∀ j ∉ O, ∃ t : ℤ, V j = latHalfPlane (!D.eps j) (D.v j) t ∧
      FullyPeriodicOn (D.G j) (V j)) :
    ∃ (b c : Fin n) (d : ℤ × ℤ), b ∈ O ∧ c ≠ b ∧ d ≠ 0 ∧ D.Fixes d c ∧
      piE (D.eps b) (D.v b) d < 0 ∧ ∀ j, j ≠ b → j ≠ c → SafeFor (D.G j) d := by
  classical
  by_cases hOcard : O.card = 1
  · -- **`O.card = 1`, elementary construction** (paper, the degenerate-sector case): write
    -- `O = {b}`, pick any `c ≠ b`.  Choose the sign `ε` of `d`'s multiple of `D.h c` so that
    -- `π_b (ε • D.h c) < 0`; every other `j ≠ b, c` is already ∉ `O`, hence has *both* sides
    -- `D.U j` and `V j` fully periodic, and `π_j (ε • D.h c) ≠ 0` since `D.v j ∦ D.v c`, so one
    -- of the two sides always has the correct sign for `j` regardless of `ε`.  A single common
    -- scalar `N` (via `exists_common_smul_mem_Per_pos`) then lands `d := N • (ε • D.h c)` in
    -- every resolved `j`'s global-extension period lattice, making `d` safe for all of them.
    obtain ⟨b, hOeq⟩ := Finset.card_eq_one.mp hOcard
    have hbO : b ∈ O := by rw [hOeq]; exact Finset.mem_singleton_self b
    have hnt : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr D.two_le
    obtain ⟨c, hcb⟩ := exists_ne b
    have hbc : b ≠ c := hcb.symm
    have hjnotO : ∀ j : Fin n, j ≠ b → j ∉ O := by
      intro j hj hjO
      rw [hOeq, Finset.mem_singleton] at hjO
      exact hj hjO
    have hepsb : D.eps b = true := hnorm b
    have hkc_ne : (D.k c : ℤ) ≠ 0 := by exact_mod_cast (D.k_pos c).ne'
    have hdetbc : det (D.v b) (D.v c) ≠ 0 := D.nonparallel hbc
    set pib : ℤ := pi (D.v b) (D.h c) with hpibdef
    have hpib_ne : pib ≠ 0 := by
      rw [hpibdef]
      show pi (D.v b) ((D.k c : ℤ) • D.v c) ≠ 0
      rw [pi_smul]
      exact mul_ne_zero hkc_ne hdetbc
    set ε : ℤ := if 0 < pib then -1 else 1 with hεdef
    have hεpib : ε * pib < 0 := by
      rw [hεdef]; split_ifs with h
      · nlinarith
      · have h' : pib < 0 := lt_of_le_of_ne (not_lt.mp h) hpib_ne
        nlinarith
    have hεne : ε ≠ 0 := by rw [hεdef]; split_ifs <;> norm_num
    -- every resolved `j ≠ b, c` supplies a doubly periodic global extension on whichever side
    -- of `D.G j` matches the sign of `π_j (ε • D.h c)`.
    have hjex : ∀ j : Fin n, j ≠ b → j ≠ c → ∃ (σ : Bool) (t : ℤ) (G' : Config (ZMod p)),
        FullyPeriodicOn (D.G j) (latHalfPlane σ (D.v j) t) ∧ DoublyPeriodic G' ∧
        (∀ z ∈ latHalfPlane σ (D.v j) t, G' z = D.G j z) ∧
        0 < piE σ (D.v j) (ε • D.h c) := by
      intro j hjb hjc
      have hjO : j ∉ O := hjnotO j hjb
      have hepsj : D.eps j = true := hnorm j
      have hvjprim : Primitive (D.v j) := D.primitive j
      have hdetjc : det (D.v j) (D.v c) ≠ 0 := D.nonparallel hjc
      have hpij : pi (D.v j) (ε • D.h c) = ε * (D.k c : ℤ) * det (D.v j) (D.v c) := by
        show pi (D.v j) (ε • ((D.k c : ℤ) • D.v c)) = ε * (D.k c : ℤ) * det (D.v j) (D.v c)
        rw [smul_smul, pi_smul]; rfl
      have hpijne : pi (D.v j) (ε • D.h c) ≠ 0 :=
        hpij ▸ mul_ne_zero (mul_ne_zero hεne hkc_ne) hdetjc
      by_cases hsign : 0 < pi (D.v j) (ε • D.h c)
      · have hfpU : FullyPeriodicOn (D.G j) (latHalfPlane true (D.v j) (D.t j)) := by
          rw [← hepsj]; exact D.fullyPeriodic_U j
        obtain ⟨hh, hh', hfpW⟩ := hfpU
        have hRhalf : IsHalfPlane (latHalfPlane true (D.v j) (D.t j)) :=
          isHalfPlane_latHalfPlane hvjprim.ne_zero true (D.t j)
        have hRne : (latHalfPlane true (D.v j) (D.t j)).Nonempty :=
          latHalfPlane_nonempty hvjprim true (D.t j)
        refine ⟨true, D.t j, globalExt (D.G j) _ (Or.inr hRhalf) hRne hfpW, ⟨hh, hh', hfpW⟩,
          (globalExt_spec (Or.inr hRhalf) hRne hfpW).1,
          (globalExt_spec (Or.inr hRhalf) hRne hfpW).2, hsign⟩
      · have hsign' : 0 < -(pi (D.v j) (ε • D.h c)) := by
          have hle : pi (D.v j) (ε • D.h c) ≤ 0 := not_lt.mp hsign
          have hlt : pi (D.v j) (ε • D.h c) < 0 := lt_of_le_of_ne hle hpijne
          linarith
        obtain ⟨tj, hVeq, hfpV⟩ := hV j hjO
        have hVeq' : V j = latHalfPlane false (D.v j) tj := by rw [hVeq, hepsj]; rfl
        have hfpV' : FullyPeriodicOn (D.G j) (latHalfPlane false (D.v j) tj) := hVeq' ▸ hfpV
        obtain ⟨hh, hh', hfpW⟩ := hfpV'
        have hRhalf : IsHalfPlane (latHalfPlane false (D.v j) tj) :=
          isHalfPlane_latHalfPlane hvjprim.ne_zero false tj
        have hRne : (latHalfPlane false (D.v j) tj).Nonempty :=
          latHalfPlane_nonempty hvjprim false tj
        refine ⟨false, tj, globalExt (D.G j) _ (Or.inr hRhalf) hRne hfpW, ⟨hh, hh', hfpW⟩,
          (globalExt_spec (Or.inr hRhalf) hRne hfpW).1,
          (globalExt_spec (Or.inr hRhalf) hRne hfpW).2, hsign'⟩
    have hjex' : ∀ j : Fin n, ∃ (σ : Bool) (t : ℤ) (G' : Config (ZMod p)),
        (j ≠ b ∧ j ≠ c) → FullyPeriodicOn (D.G j) (latHalfPlane σ (D.v j) t) ∧
          DoublyPeriodic G' ∧ (∀ z ∈ latHalfPlane σ (D.v j) t, G' z = D.G j z) ∧
          0 < piE σ (D.v j) (ε • D.h c) := by
      intro j
      by_cases hj : j ≠ b ∧ j ≠ c
      · obtain ⟨σ, t, G', h1, h2, h3, h4⟩ := hjex j hj.1 hj.2
        exact ⟨σ, t, G', fun _ => ⟨h1, h2, h3, h4⟩⟩
      · exact ⟨true, 0, 0, fun hcon => absurd hcon hj⟩
    choose σfun tfun Gfun hspec using hjex'
    set OC : Finset (Fin n) := Finset.univ.filter (fun j => j ≠ b ∧ j ≠ c) with hOCdef
    set Ω : Finset (Config (ZMod p)) := OC.image Gfun with hΩdef
    have hΩdp : ∀ y ∈ (↑Ω : Set (Config (ZMod p))), DoublyPeriodic y := by
      intro y hy
      rw [hΩdef, Finset.coe_image] at hy
      obtain ⟨j, hj, hjy⟩ := hy
      have hjbc : j ≠ b ∧ j ≠ c := (Finset.mem_filter.mp hj).2
      rw [← hjy]; exact (hspec j hjbc).2.1
    obtain ⟨Ncommon, hNpos, hNmem⟩ :=
      exists_common_smul_mem_Per_pos (Ω : Finset (Config (ZMod p))).finite_toSet hΩdp
    have hNcommon_mem : ∀ j : Fin n, (j ≠ b ∧ j ≠ c) → ∀ w : ℤ × ℤ, (Ncommon : ℤ) • w ∈ Per (Gfun j) := by
      intro j hjbc w
      have hjOC : j ∈ OC := by rw [hOCdef]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjbc⟩
      have hmemΩ : Gfun j ∈ (↑Ω : Set (Config (ZMod p))) := by
        rw [hΩdef, Finset.coe_image]; exact ⟨j, hjOC, rfl⟩
      exact hNmem (Gfun j) hmemΩ w
    -- assemble `d := Ncommon • (ε • D.h c)`
    set d : ℤ × ℤ := (Ncommon : ℤ) • (ε • D.h c) with hddef
    have hNcommon_ne : (Ncommon : ℤ) ≠ 0 := by exact_mod_cast hNpos.ne'
    have hdne : d ≠ 0 := smul_ne_zero hNcommon_ne (smul_ne_zero hεne (D.h_ne_zero c))
    have hdeq : d = (Ncommon * ε) • D.h c := by rw [hddef, smul_smul]
    have hfixdet : det (D.v c) d = 0 := by
      have heq : d = (Ncommon * ε * (D.k c : ℤ)) • D.v c := by
        rw [hdeq]; show (Ncommon * ε) • ((D.k c : ℤ) • D.v c) = _; rw [smul_smul]
      rw [heq]; simp [det, Prod.smul_def]; ring
    have hfixper : d ∈ Per (D.G c) := by
      rw [hdeq]; exact (Per (D.G c)).zsmul_mem (D.h_mem_Per c) _
    have hnegb : piE (D.eps b) (D.v b) d < 0 := by
      rw [hepsb]
      show pi (D.v b) d < 0
      rw [hddef, pi_smul, pi_smul]
      have : (Ncommon : ℤ) * (ε * pib) < 0 :=
        mul_neg_of_pos_of_neg (by exact_mod_cast hNpos) hεpib
      rw [hpibdef] at this
      linarith [this]
    refine ⟨b, c, d, hbO, hbc.symm, hdne, ⟨hfixdet, hfixper⟩, hnegb, fun j hjb hjc => ?_⟩
    have hjbc : j ≠ b ∧ j ≠ c := ⟨hjb, hjc⟩
    obtain ⟨hfp, hdp, hext, hpos⟩ := hspec j hjbc
    have hdpos : 0 < piE (σfun j) (D.v j) d := by
      rw [hddef, piE_zsmul]
      exact mul_pos (by exact_mod_cast hNpos) hpos
    have hdper : d ∈ Per (Gfun j) := hddef ▸ hNcommon_mem j hjbc (ε • D.h c)
    exact safeFor_of_fullyPeriodic hfp hdp hext hdpos hdper
  · -- **`O.card ≥ 2`**: use the angular order tool `exists_angular_min` (`Nivat/RayOrder.lean`)
    -- twice: once to pick out the angularly-first element `b` of `O`, from a reference direction
    -- `e` that lies strictly on the same side of *every* `v_j` (`j : Fin n`) — obtained from the
    -- two spanning rays `w1, w2` of the common recession cone `D.K` via `D.K_side` — and once
    -- more, among those directions strictly past `b`, to pick out the next one `c`.  Every
    -- remaining `j ∈ O ∖ {b, c}` then lies strictly past `c` as well, forcing the sign needed to
    -- replace the (trivial, in the `O.card = 1` case) fact `j ∉ O`.
    obtain ⟨w1, w2, hw12det, hKeq⟩ := D.K_sector
    have hw1K : w1 ∈ D.K := by rw [hKeq]; exact ⟨1, 0, zero_le_one, le_refl (0 : ℝ), by simp⟩
    have hw2K : w2 ∈ D.K := by rw [hKeq]; exact ⟨0, 1, le_refl (0 : ℝ), zero_le_one, by simp⟩
    have ne_zero_piR_or_piR : ∀ {v : ℤ × ℤ}, v ≠ 0 → piR v w1 ≠ 0 ∨ piR v w2 ≠ 0 := by
      intro v hv
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2⟩ := hcon
      have e1 : (v.1 : ℝ) * w1.2 - (v.2 : ℝ) * w1.1 = 0 := h1
      have e2 : (v.1 : ℝ) * w2.2 - (v.2 : ℝ) * w2.1 = 0 := h2
      have hv1 : (v.1 : ℝ) * (w1.1 * w2.2 - w1.2 * w2.1) = 0 := by
        linear_combination w1.1 * e2 - w2.1 * e1
      have hv2 : (v.2 : ℝ) * (w1.1 * w2.2 - w1.2 * w2.1) = 0 := by
        linear_combination w1.2 * e2 - w2.2 * e1
      have hv1' : (v.1 : ℝ) = 0 := (mul_eq_zero.mp hv1).resolve_right hw12det
      have hv2' : (v.2 : ℝ) = 0 := (mul_eq_zero.mp hv2).resolve_right hw12det
      exact hv (Prod.ext (by exact_mod_cast hv1') (by exact_mod_cast hv2'))
    -- every component's direction lies strictly on the positive side of `w1 + w2`
    have hipos : ∀ i : Fin n, 0 < piR (D.v i) (w1 + w2) := by
      intro i
      have h1 : 0 ≤ piR (D.v i) w1 := by
        have h := D.K_side i w1 hw1K
        rw [hnorm i] at h
        exact h
      have h2 : 0 ≤ piR (D.v i) w2 := by
        have h := D.K_side i w2 hw2K
        rw [hnorm i] at h
        exact h
      have hadd : piR (D.v i) (w1 + w2) = piR (D.v i) w1 + piR (D.v i) w2 := by
        simp only [piR, Prod.fst_add, Prod.snd_add]; ring
      rw [hadd]
      rcases ne_zero_piR_or_piR (D.primitive i).ne_zero with hne | hne
      · have h1' : 0 < piR (D.v i) w1 := lt_of_le_of_ne h1 (Ne.symm hne)
        linarith
      · have h2' : 0 < piR (D.v i) w2 := lt_of_le_of_ne h2 (Ne.symm hne)
        linarith
    set e : ℝ × ℝ := -(w1 + w2) with hedef
    have hInFirst : ∀ i : Fin n, InFirstHalf e (toReal (D.v i)) := by
      intro i
      refine Or.inl ?_
      have heq : det₂ e (toReal (D.v i)) = piR (D.v i) (w1 + w2) := by
        rw [hedef]
        simp only [det₂, toReal, Prod.fst_neg, Prod.snd_neg, Prod.fst_add, Prod.snd_add, piR]
        ring
      rw [heq]; exact hipos i
    have hposOfInFirst : ∀ {x y : Fin n}, x ≠ y →
        InFirstHalf (toReal (D.v x)) (toReal (D.v y)) → 0 < pi (D.v x) (D.v y) := by
      intro x y hxy hIF
      have hdxy : det (D.v x) (D.v y) ≠ 0 := D.nonparallel hxy
      have hcast : det₂ (toReal (D.v x)) (toReal (D.v y)) = ((det (D.v x) (D.v y) : ℤ) : ℝ) :=
        det₂_toReal (D.v x) (D.v y)
      rcases hIF with hpos | ⟨hz, -⟩
      · rw [hcast] at hpos
        show (0 : ℤ) < det (D.v x) (D.v y)
        exact_mod_cast hpos
      · exfalso; rw [hcast] at hz; exact hdxy (by exact_mod_cast hz)
    obtain ⟨b, hbO, hbmin⟩ :=
      exists_angular_min (fun i => toReal (D.v i)) e O hO (fun i _ => hInFirst i)
    have hbj_pos : ∀ j ∈ O, j ≠ b → 0 < pi (D.v b) (D.v j) := fun j hjO hjb =>
      hposOfInFirst hjb.symm (hbmin j hjO)
    have h0 : 0 < O.card := Finset.card_pos.mpr hO
    have hOcard2 : 2 ≤ O.card := by omega
    have hOb : (O.erase b).Nonempty := by
      have hcard : (O.erase b).card = O.card - 1 := Finset.card_erase_of_mem hbO
      exact Finset.card_pos.mp (by omega)
    set S' : Finset (Fin n) := Finset.univ.filter (fun i => i ≠ b ∧ 0 < pi (D.v b) (D.v i))
      with hS'def
    have hS'sub : O.erase b ⊆ S' := by
      intro j hj
      rw [Finset.mem_erase] at hj
      rw [hS'def, Finset.mem_filter]
      exact ⟨Finset.mem_univ j, hj.1, hbj_pos j hj.2 hj.1⟩
    obtain ⟨j0, hj0⟩ := hOb
    have hS'ne : S'.Nonempty := ⟨j0, hS'sub hj0⟩
    obtain ⟨c, hcS', hcmin⟩ :=
      exists_angular_min (fun i => toReal (D.v i)) e S' hS'ne (fun i _ => hInFirst i)
    obtain ⟨hcb, hbc_pos⟩ := (Finset.mem_filter.mp hcS').2
    have hcj_pos : ∀ j ∈ S', j ≠ c → 0 < pi (D.v c) (D.v j) := fun j hjS' hjc =>
      hposOfInFirst hjc.symm (hcmin j hjS')
    have piSwap : ∀ u v : ℤ × ℤ, pi u v = - pi v u := by intro u v; simp only [pi, det]; ring
    have hbc : b ≠ c := hcb.symm
    have hepsb : D.eps b = true := hnorm b
    have hkc_pos : (0 : ℤ) < (D.k c : ℤ) := by exact_mod_cast (D.k_pos c)
    have hkc_ne : (D.k c : ℤ) ≠ 0 := hkc_pos.ne'
    have hdetbc : det (D.v b) (D.v c) ≠ 0 := D.nonparallel hbc
    set pib : ℤ := pi (D.v b) (D.h c) with hpibdef
    have hpib_pos : 0 < pib := by
      rw [hpibdef]
      show 0 < pi (D.v b) ((D.k c : ℤ) • D.v c)
      rw [pi_smul]
      exact mul_pos hkc_pos hbc_pos
    set ε : ℤ := -1 with hεdef
    have hεpib : ε * pib < 0 := by
      rw [hεdef]
      have heq : (-1 : ℤ) * pib = -pib := by ring
      rw [heq]; linarith [hpib_pos]
    have hεne : ε ≠ 0 := by rw [hεdef]; norm_num
    have hjex : ∀ j : Fin n, j ≠ b → j ≠ c → ∃ (σ : Bool) (t : ℤ) (G' : Config (ZMod p)),
        FullyPeriodicOn (D.G j) (latHalfPlane σ (D.v j) t) ∧ DoublyPeriodic G' ∧
        (∀ z ∈ latHalfPlane σ (D.v j) t, G' z = D.G j z) ∧
        0 < piE σ (D.v j) (ε • D.h c) := by
      intro j hjb hjc
      have hepsj : D.eps j = true := hnorm j
      have hvjprim : Primitive (D.v j) := D.primitive j
      have hdetjc : det (D.v j) (D.v c) ≠ 0 := D.nonparallel hjc
      have hpij : pi (D.v j) (ε • D.h c) = ε * (D.k c : ℤ) * det (D.v j) (D.v c) := by
        show pi (D.v j) (ε • ((D.k c : ℤ) • D.v c)) = ε * (D.k c : ℤ) * det (D.v j) (D.v c)
        rw [smul_smul, pi_smul]; rfl
      have hpijne : pi (D.v j) (ε • D.h c) ≠ 0 :=
        hpij ▸ mul_ne_zero (mul_ne_zero hεne hkc_ne) hdetjc
      by_cases hsign : 0 < pi (D.v j) (ε • D.h c)
      · have hfpU : FullyPeriodicOn (D.G j) (latHalfPlane true (D.v j) (D.t j)) := by
          rw [← hepsj]; exact D.fullyPeriodic_U j
        obtain ⟨hh, hh', hfpW⟩ := hfpU
        have hRhalf : IsHalfPlane (latHalfPlane true (D.v j) (D.t j)) :=
          isHalfPlane_latHalfPlane hvjprim.ne_zero true (D.t j)
        have hRne : (latHalfPlane true (D.v j) (D.t j)).Nonempty :=
          latHalfPlane_nonempty hvjprim true (D.t j)
        refine ⟨true, D.t j, globalExt (D.G j) _ (Or.inr hRhalf) hRne hfpW, ⟨hh, hh', hfpW⟩,
          (globalExt_spec (Or.inr hRhalf) hRne hfpW).1,
          (globalExt_spec (Or.inr hRhalf) hRne hfpW).2, hsign⟩
      · have hjO : j ∉ O := by
          intro hjOmem
          apply hsign
          have hjS' : j ∈ S' := hS'sub (Finset.mem_erase.mpr ⟨hjb, hjOmem⟩)
          have hcjpos : 0 < pi (D.v c) (D.v j) := hcj_pos j hjS' hjc
          have hjcneg : pi (D.v j) (D.v c) < 0 := by
            rw [piSwap (D.v j) (D.v c)]; linarith
          have hjcneg' : det (D.v j) (D.v c) < 0 := hjcneg
          rw [hpij, hεdef]
          have heq : (-1 : ℤ) * (D.k c : ℤ) * det (D.v j) (D.v c) =
              (D.k c : ℤ) * (-(det (D.v j) (D.v c))) := by ring
          rw [heq]
          exact mul_pos hkc_pos (by linarith [hjcneg'])
        have hsign' : 0 < -(pi (D.v j) (ε • D.h c)) := by
          have hle : pi (D.v j) (ε • D.h c) ≤ 0 := not_lt.mp hsign
          have hlt : pi (D.v j) (ε • D.h c) < 0 := lt_of_le_of_ne hle hpijne
          linarith
        obtain ⟨tj, hVeq, hfpV⟩ := hV j hjO
        have hVeq' : V j = latHalfPlane false (D.v j) tj := by rw [hVeq, hepsj]; rfl
        have hfpV' : FullyPeriodicOn (D.G j) (latHalfPlane false (D.v j) tj) := hVeq' ▸ hfpV
        obtain ⟨hh, hh', hfpW⟩ := hfpV'
        have hRhalf : IsHalfPlane (latHalfPlane false (D.v j) tj) :=
          isHalfPlane_latHalfPlane hvjprim.ne_zero false tj
        have hRne : (latHalfPlane false (D.v j) tj).Nonempty :=
          latHalfPlane_nonempty hvjprim false tj
        exact ⟨false, tj, globalExt (D.G j) _ (Or.inr hRhalf) hRne hfpW, ⟨hh, hh', hfpW⟩,
          (globalExt_spec (Or.inr hRhalf) hRne hfpW).1,
          (globalExt_spec (Or.inr hRhalf) hRne hfpW).2, hsign'⟩
    have hjex' : ∀ j : Fin n, ∃ (σ : Bool) (t : ℤ) (G' : Config (ZMod p)),
        (j ≠ b ∧ j ≠ c) → FullyPeriodicOn (D.G j) (latHalfPlane σ (D.v j) t) ∧
          DoublyPeriodic G' ∧ (∀ z ∈ latHalfPlane σ (D.v j) t, G' z = D.G j z) ∧
          0 < piE σ (D.v j) (ε • D.h c) := by
      intro j
      by_cases hj : j ≠ b ∧ j ≠ c
      · obtain ⟨σ, t, G', h1, h2, h3, h4⟩ := hjex j hj.1 hj.2
        exact ⟨σ, t, G', fun _ => ⟨h1, h2, h3, h4⟩⟩
      · exact ⟨true, 0, 0, fun hcon => absurd hcon hj⟩
    choose σfun tfun Gfun hspec using hjex'
    set OC : Finset (Fin n) := Finset.univ.filter (fun j => j ≠ b ∧ j ≠ c) with hOCdef
    set Ω : Finset (Config (ZMod p)) := OC.image Gfun with hΩdef
    have hΩdp : ∀ y ∈ (↑Ω : Set (Config (ZMod p))), DoublyPeriodic y := by
      intro y hy
      rw [hΩdef, Finset.coe_image] at hy
      obtain ⟨j, hj, hjy⟩ := hy
      have hjbc : j ≠ b ∧ j ≠ c := (Finset.mem_filter.mp hj).2
      rw [← hjy]; exact (hspec j hjbc).2.1
    obtain ⟨Ncommon, hNpos, hNmem⟩ :=
      exists_common_smul_mem_Per_pos (Ω : Finset (Config (ZMod p))).finite_toSet hΩdp
    have hNcommon_mem : ∀ j : Fin n, (j ≠ b ∧ j ≠ c) → ∀ w : ℤ × ℤ,
        (Ncommon : ℤ) • w ∈ Per (Gfun j) := by
      intro j hjbc w
      have hjOC : j ∈ OC := by rw [hOCdef]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjbc⟩
      have hmemΩ : Gfun j ∈ (↑Ω : Set (Config (ZMod p))) := by
        rw [hΩdef, Finset.coe_image]; exact ⟨j, hjOC, rfl⟩
      exact hNmem (Gfun j) hmemΩ w
    set d : ℤ × ℤ := (Ncommon : ℤ) • (ε • D.h c) with hddef
    have hNcommon_ne : (Ncommon : ℤ) ≠ 0 := by exact_mod_cast hNpos.ne'
    have hdne : d ≠ 0 := smul_ne_zero hNcommon_ne (smul_ne_zero hεne (D.h_ne_zero c))
    have hdeq : d = (Ncommon * ε) • D.h c := by rw [hddef, smul_smul]
    have hfixdet : det (D.v c) d = 0 := by
      have heq : d = (Ncommon * ε * (D.k c : ℤ)) • D.v c := by
        rw [hdeq]; show (Ncommon * ε) • ((D.k c : ℤ) • D.v c) = _; rw [smul_smul]
      rw [heq]; simp [det, Prod.smul_def]; ring
    have hfixper : d ∈ Per (D.G c) := by
      rw [hdeq]; exact (Per (D.G c)).zsmul_mem (D.h_mem_Per c) _
    have hnegb : piE (D.eps b) (D.v b) d < 0 := by
      rw [hepsb]
      show pi (D.v b) d < 0
      rw [hddef, pi_smul, pi_smul]
      have hlt : (Ncommon : ℤ) * (ε * pib) < 0 :=
        mul_neg_of_pos_of_neg (by exact_mod_cast hNpos) hεpib
      rw [hpibdef] at hlt
      linarith [hlt]
    refine ⟨b, c, d, hbO, hcb, hdne, ⟨hfixdet, hfixper⟩, hnegb, fun j hjb hjc => ?_⟩
    have hjbc : j ≠ b ∧ j ≠ c := ⟨hjb, hjc⟩
    obtain ⟨hfp, hdp, hext, hpos⟩ := hspec j hjbc
    have hdpos : 0 < piE (σfun j) (D.v j) d := by
      rw [hddef, piE_zsmul]
      exact mul_pos (by exact_mod_cast hNpos) hpos
    have hdper : d ∈ Per (Gfun j) := hddef ▸ hNcommon_mem j hjbc (ε • D.h c)
    exact safeFor_of_fullyPeriodic hfp hdp hext hdpos hdper

end FirstHalfPlane

/-! ### Lemma 8.16 -/

-- `Nivat.exists_mem_subseqLimits_along` (`Nivat/SubseqLimit.lean`, lineB) now supplies exactly
-- the compactness step used below; the local duplicate that used to live here has been removed.

/-- Two configurations sharing the period `k • v` (`k > 0`) that agree along a fixed line
`z₀ + ℤv` at the `k` consecutive points `s = 0, …, k − 1` agree at *every* integer point of that
line.  Paper §8.4/Lemma 8.16: "two fields of period `kv` that agree at `k` consecutive lattice
points of a row agree on the whole row." -/
private theorem eq_of_period_agree_consecutive {p : ℕ} {y1 y2 : Config (ZMod p)} {k : ℕ}
    (hk : 0 < k) {v z0 : ℤ × ℤ} (hper1 : (k : ℤ) • v ∈ Per y1) (hper2 : (k : ℤ) • v ∈ Per y2)
    (hagree : ∀ s : ℤ, 0 ≤ s → s < k → y1 (z0 + s • v) = y2 (z0 + s • v)) (s : ℤ) :
    y1 (z0 + s • v) = y2 (z0 + s • v) := by
  set r : ℤ := s % (k : ℤ) with hrdef
  set m : ℤ := s / (k : ℤ) with hmdef
  have hkpos : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  have hr0 : 0 ≤ r := Int.emod_nonneg s (by omega)
  have hrk : r < (k : ℤ) := Int.emod_lt_of_pos s hkpos
  have hsplit : (k : ℤ) * m + r = s := Int.mul_ediv_add_emod s (k : ℤ)
  have hs : s = (k : ℤ) * m + r := hsplit.symm
  have hzeq : z0 + s • v = z0 + r • v + m • ((k : ℤ) • v) := by
    rw [hs, smul_smul]; module
  have h1 : y1 (z0 + r • v + m • ((k : ℤ) • v)) = y1 (z0 + r • v) :=
    Per.apply ((Per y1).zsmul_mem hper1 m) (z0 + r • v)
  have h2 : y2 (z0 + r • v + m • ((k : ℤ) • v)) = y2 (z0 + r • v) :=
    Per.apply ((Per y2).zsmul_mem hper2 m) (z0 + r • v)
  rw [hzeq, h1, h2]
  exact hagree r hr0 hrk

/-- Translating a configuration transports its periods: `w ∈ Per f → w ∈ Per (T e f)`. -/
private theorem mem_Per_T_of_mem_Per {p : ℕ} {f : Config (ZMod p)} (e : ℤ × ℤ) {w : ℤ × ℤ}
    (hw : w ∈ Per f) : w ∈ Per (T e f) := by
  rw [mem_Per_iff]
  have h1 : T (w + e) f = T e f := by
    rw [add_comm w e, T_add e w f, mem_Per_iff.mp hw]
  calc T w (T e f) = T (w + e) f := (T_add w e f).symm
    _ = T e f := h1

/-- If two configurations sharing periods `k • v` and `M • u` (a unimodular basis `(v, u)`)
agree on the finite grid `{s • v + t • u : 0 ≤ s < k, 0 ≤ t < M}`, they agree everywhere.

Paper Lemma 8.16, Step 2(b)/(c): the tool used to promote agreement on a finite window to a
genuine identity of configurations, applying `eq_of_period_agree_consecutive` once along each
of the two basis directions. -/
private theorem eq_of_periods_agree_on_grid {p : ℕ} {y1 y2 : Config (ZMod p)} {v u : ℤ × ℤ}
    (hvu : det v u = 1) {k M : ℕ} (hk : 0 < k) (hM : 0 < M)
    (hper1v : (k : ℤ) • v ∈ Per y1) (hper2v : (k : ℤ) • v ∈ Per y2)
    (hper1u : (M : ℤ) • u ∈ Per y1) (hper2u : (M : ℤ) • u ∈ Per y2)
    (hgrid : ∀ s t : ℤ, 0 ≤ s → s < k → 0 ≤ t → t < M → y1 (s • v + t • u) = y2 (s • v + t • u))
    (z : ℤ × ℤ) : y1 z = y2 z := by
  have hrow : ∀ t : ℤ, 0 ≤ t → t < M → ∀ s : ℤ, y1 (t • u + s • v) = y2 (t • u + s • v) := by
    intro t ht0 htM
    have hagree0 : ∀ s' : ℤ, 0 ≤ s' → s' < k → y1 (t • u + s' • v) = y2 (t • u + s' • v) := by
      intro s' hs'0 hs'k
      rw [add_comm]
      exact hgrid s' t hs'0 hs'k ht0 htM
    exact eq_of_period_agree_consecutive hk hper1v hper2v hagree0
  have hagreeU : ∀ t' : ℤ, 0 ≤ t' → t' < M →
      y1 ((det z u) • v + t' • u) = y2 ((det z u) • v + t' • u) := by
    intro t' ht'0 ht'M
    have h := hrow t' ht'0 ht'M (det z u)
    rwa [add_comm] at h
  rw [eq_smul_add_smul hvu z]
  exact eq_of_period_agree_consecutive hM hper1u hper2u hagreeU (det v z)

/-- **Lemma 8.16, Step 2(a).**  For every finite window `B`, `T^{nd}G` eventually (in `n`) agrees
with some element of `Ω = subseqLimits G d` on `B`.

This uses only the compactness lemma `exists_mem_subseqLimits_along` (`Nivat/SubseqLimit.lean`,
lineB), not the finiteness of `Ω`: if agreement failed for an unbounded set `S` of `n`, applying
that lemma to `S` produces a subsequential limit `y' ∈ Ω` that, by construction, agrees with
`T^{nd}G` on `B` for some `n ∈ S` — contradicting `n ∈ S`. -/
private theorem exists_eventually_agree {p : ℕ} [Fact p.Prime] (G : Config (ZMod p)) (d : ℤ × ℤ)
    (B : Finset (ℤ × ℤ)) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∃ y ∈ subseqLimits G d, ∀ w ∈ B, y w = G (w + (n : ℤ) • d) := by
  by_contra hcon
  push Not at hcon
  set S : Set ℕ := {n : ℕ | ∀ y ∈ subseqLimits G d, ∃ w ∈ B, y w ≠ G (w + (n : ℤ) • d)} with hSdef
  have hSinf : S.Infinite := Set.infinite_of_not_bddAbove (by
    rintro ⟨B', hB'⟩
    obtain ⟨n, hle, hSprop⟩ := hcon (B' + 1)
    have hnS : n ∈ S := hSprop
    have hnB' : n ≤ B' := hB' hnS
    omega)
  obtain ⟨y', hy'mem, hy'prop⟩ := exists_mem_subseqLimits_along G d hSinf
  obtain ⟨n, hnS, -, hn⟩ := hy'prop B 0
  obtain ⟨w, hw, hne⟩ := hnS y' hy'mem
  exact hne (hn w hw)

/-- **Conditional version of Lemma 8.16, Step 1.** Given an explicit trace bound `P` on every
element of `Ω = subseqLimits G d` (Step 1b, `nivat.txt` ~1710+, being supplied by lineV in
`Nivat/PeriodCount.lean`), `Ω` is finite: it embeds into `finite_of_trace_le`'s finite set via
`mem_Per_of_mem_subseqLimits` (the coarse period `k • v` of `G` transmits to every subsequential
limit) together with `hlim` and the bound `hbound`. This is Step 1a plus the trivial set
inclusion; the pigeonhole argument bounding the trace itself (Step 1b) is `hbound`'s job. -/
private theorem finite_subseqLimits_of_trace_bound {p : ℕ} [Fact p.Prime] {G : Config (ZMod p)}
    {v u : ℤ × ℤ} (hvu : det v u = 1) {k : ℕ} (hk : 0 < k) (hper : ((k : ℤ) • v) ∈ Per G)
    {d : ℤ × ℤ} (hlim : ∀ y ∈ subseqLimits G d, DoublyPeriodic y)
    (P : ℕ) (hbound : ∀ y ∈ subseqLimits G d, trace v y ≤ P) :
    (subseqLimits G d).Finite := by
  have hsub : subseqLimits G d ⊆
      {y : Config (ZMod p) | ((k : ℤ) • v) ∈ Per y ∧ DoublyPeriodic y ∧ trace v y ≤ P} := by
    intro y hy
    exact ⟨mem_Per_of_mem_subseqLimits hy hper, hlim y hy, hbound y hy⟩
  exact (finite_of_trace_le hvu hk P).subset hsub

theorem finite_subseqLimits {p : ℕ} [Fact p.Prime] {G : Config (ZMod p)}
    {v u : ℤ × ℤ} (hvu : det v u = 1) {k : ℕ} (hk : 0 < k) (hper : ((k : ℤ) • v) ∈ Per G)
    {d : ℤ × ℤ} (hd : 0 < -(pi v d))
    (hlim : ∀ y ∈ subseqLimits G d, DoublyPeriodic y) :
    (subseqLimits G d).Finite :=
  finite_subseqLimits_of_doublyPeriodic hvu hk hper hd hlim

/-- **Lemma 8.16 (Propagation).**  Let `G : ℤ² → 𝔽_p` have period `kv` with `v` primitive and
`k ≥ 1`, let `(v, u)` be a unimodular basis and put `φ = π_v`.  Let `d` satisfy
`δ = −φ(d) > 0`.  If every subsequential limit of `(T^{nd}G)` is doubly periodic, then there are
`τ ∈ ℤ` and a doubly periodic `Ĝ` with `G = Ĝ` on `{φ ≤ τ}`.

The proof shows first that the limit set `Ω` is finite — otherwise a field of arbitrarily large
"trace" would converge to one of finite trace, producing a point where a period of the limit
fails — and then that `T^d` acts on `Ω` compatibly with the translates of `G`. -/
theorem exists_doublyPeriodic_agree {p : ℕ} [Fact p.Prime] {G : Config (ZMod p)}
    {v u : ℤ × ℤ} (hvu : det v u = 1) {k : ℕ} (hk : 0 < k) (hper : ((k : ℤ) • v) ∈ Per G)
    {d : ℤ × ℤ} (hd : 0 < -(pi v d))
    (hlim : ∀ y ∈ subseqLimits G d, DoublyPeriodic y) :
    ∃ (τ : ℤ) (Gd : Config (ZMod p)), DoublyPeriodic Gd ∧ ∀ z, pi v z ≤ τ → G z = Gd z := by
  -- **Step 1.**  `Ω := subseqLimits G d` is finite (`finite_subseqLimits`), every element
  -- inherits the coarse period `k • v` from `G` (`mem_Per_of_mem_subseqLimits`), and every
  -- element is doubly periodic (`hlim`); a common secondary period scalar `Na` for all of `Ω`
  -- (in every direction, in particular `u`) comes from `exists_common_smul_mem_Per_pos`.
  set Ω : Set (Config (ZMod p)) := subseqLimits G d with hΩdef
  have hΩfin : Ω.Finite := finite_subseqLimits hvu hk hper hd hlim
  have hΩdp : ∀ y ∈ Ω, DoublyPeriodic y := hlim
  have hΩper : ∀ y ∈ Ω, (k : ℤ) • v ∈ Per y := fun y hy => mem_Per_of_mem_subseqLimits hy hper
  obtain ⟨Na, hNapos, hNamem⟩ := exists_common_smul_mem_Per_pos hΩfin hΩdp
  -- Enlarge `Na` to `M := Na * δ.toNat` so that `M • u` is still a common period of every
  -- element of `Ω`, and `δ ≤ M` (needed below so the remainder of Euclidean division by `δ`
  -- always lands inside `[0, M)`).
  set δ : ℤ := -(pi v d) with hδdef
  have hδpos : 0 < δ := hd
  set δN : ℕ := δ.toNat with hδNdef
  have hδNcast : (δN : ℤ) = δ := Int.toNat_of_nonneg hδpos.le
  have hδNpos : 0 < δN := by
    have : (0 : ℤ) < (δN : ℤ) := hδNcast ▸ hδpos
    exact_mod_cast this
  set M : ℕ := Na * δN with hMdef
  have hMpos : 0 < M := Nat.mul_pos hNapos hδNpos
  have hMcast : (M : ℤ) = (Na : ℤ) * δ := by rw [hMdef]; push_cast; rw [hδNcast]
  have hMge : δ ≤ (M : ℤ) := by
    have hNa1 : (1 : ℤ) ≤ (Na : ℤ) := by exact_mod_cast hNapos
    rw [hMcast]; nlinarith [hδpos]
  have hMmem : ∀ y ∈ Ω, ∀ w : ℤ × ℤ, (M : ℤ) • w ∈ Per y := by
    intro y hy w
    have heq : (M : ℤ) • w = δ • ((Na : ℤ) • w) := by rw [hMcast, mul_comm, mul_smul]
    rw [heq]
    exact (Per y).zsmul_mem (hNamem y hy w) δ
  -- The finite grid used both to detect agreement (Step 2(a)) and, via `eq_of_periods_agree_on_grid`,
  -- to upgrade grid-agreement to full agreement (Step 2(b)).
  set B : Finset (ℤ × ℤ) :=
    (Finset.Ico (0 : ℤ) (k : ℤ) ×ˢ Finset.Ico (0 : ℤ) (M : ℤ)).image
      (fun st => st.1 • v + st.2 • u) with hBdef
  set B2 : Finset (ℤ × ℤ) := B ∪ B.image (· + d) with hB2def
  -- **Step 2(a).**  For all sufficiently large `n`, `T^{nd}G` agrees with *some* element of `Ω`
  -- on the (finite) window `B2`.
  obtain ⟨N0, hN0⟩ := exists_eventually_agree G d B2
  choose Y hYmem hYspec using fun off : ℕ => hN0 (N0 + off) (Nat.le_add_right N0 off)
  -- `Y off ∈ Ω` and `Y off` agrees with `G (· + (N0 + off) • d)` on `B2`, for every `off : ℕ`.
  -- **Step 2(b).**  Consecutive `Y off`s are linked by exactly one `T^d`-shift: the windows for
  -- `off` and `off + 1` overlap on the whole grid `B` (via `B2 = B ∪ (B + d)`), and both
  -- `T d (Y off)` and `Y (off + 1)` share the periods `k • v` and `M • u`, so
  -- `eq_of_periods_agree_on_grid` upgrades the grid-agreement to full agreement.
  have hYshift : ∀ off : ℕ, T d (Y off) = Y (off + 1) := by
    intro off
    have hgrid' : ∀ s t : ℤ, 0 ≤ s → s < k → 0 ≤ t → t < M →
        (T d (Y off)) (s • v + t • u) = Y (off + 1) (s • v + t • u) := by
      intro s t hs0 hsk ht0 htM
      show Y off (s • v + t • u + d) = Y (off + 1) (s • v + t • u)
      have hmemB : s • v + t • u ∈ B := by
        rw [hBdef, Finset.mem_image]
        exact ⟨(s, t), Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ⟨hs0, hsk⟩,
          Finset.mem_Ico.mpr ⟨ht0, htM⟩⟩, rfl⟩
      have hmemB2 : s • v + t • u ∈ B2 := by
        rw [hB2def]; exact Finset.mem_union_left _ hmemB
      have hmemB2' : s • v + t • u + d ∈ B2 := by
        rw [hB2def]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hmemB)
      have h1 : Y off (s • v + t • u + d) =
          G (s • v + t • u + d + ((N0 + off : ℕ) : ℤ) • d) := hYspec off _ hmemB2'
      have h2 : Y (off + 1) (s • v + t • u) =
          G (s • v + t • u + ((N0 + off + 1 : ℕ) : ℤ) • d) := hYspec (off + 1) _ hmemB2
      rw [h1, h2]
      congr 1
      push_cast
      ring
    have hper1v : (k : ℤ) • v ∈ Per (T d (Y off)) :=
      mem_Per_T_of_mem_Per d (hΩper (Y off) (hYmem off))
    have hper2v : (k : ℤ) • v ∈ Per (Y (off + 1)) := hΩper (Y (off + 1)) (hYmem (off + 1))
    have hper1u : (M : ℤ) • u ∈ Per (T d (Y off)) :=
      mem_Per_T_of_mem_Per d (hMmem (Y off) (hYmem off) u)
    have hper2u : (M : ℤ) • u ∈ Per (Y (off + 1)) := hMmem (Y (off + 1)) (hYmem (off + 1)) u
    funext z
    exact eq_of_periods_agree_on_grid hvu hk hMpos hper1v hper2v hper1u hper2u hgrid' z
  -- **Step 2(c).**  Telescoping: `Y off = T^{off • d} (Y 0)` for every `off`.
  have hYchain : ∀ off : ℕ, Y off = T ((off : ℤ) • d) (Y 0) := by
    intro off
    induction off with
    | zero => simp
    | succ m ih =>
      rw [← hYshift m, ih]
      have : ((↑(m + 1) : ℤ) • d) = d + (m : ℤ) • d := by push_cast; module
      rw [this, T_add]
  -- **Assembly.**  `Gd := T^{-N0 • d} (Y 0)` is doubly periodic (periods transported by
  -- `mem_Per_T_of_mem_Per`), and agrees with `G` on `{π_v ≤ τ}` for `τ := -N0 * δ`: given `z`
  -- with `π_v z ≤ τ`, Euclidean division of `π_v z` by `δ` produces `n := -(π_v z / δ)` with
  -- `n ≥ N0`; the point `w := z - n • d` then has `π_v w = π_v z % δ ∈ [0, δ) ⊆ [0, M)`, so
  -- Step 2(a)'s window-agreement (extended along the `v`-row via `eq_of_period_agree_consecutive`)
  -- identifies `G z = Y (n - N0) w` with the value of the telescoped, fixed `Gd` at `z`.
  set Gd : Config (ZMod p) := T (-(N0 : ℤ) • d) (Y 0) with hGddef
  have hGddp : DoublyPeriodic Gd := by
    obtain ⟨a, ha, b, hb, hdetab⟩ := hΩdp (Y 0) (hYmem 0)
    exact ⟨a, mem_Per_T_of_mem_Per _ ha, b, mem_Per_T_of_mem_Per _ hb, hdetab⟩
  set τ : ℤ := -(N0 : ℤ) * δ with hτdef
  refine ⟨τ, Gd, hGddp, fun z hz => ?_⟩
  set r : ℤ := (pi v z) % δ with hrdef
  set m : ℤ := (pi v z) / δ with hmdef
  have hsplit : δ * m + r = pi v z := Int.mul_ediv_add_emod (pi v z) δ
  have hr0 : 0 ≤ r := Int.emod_nonneg (pi v z) hδpos.ne'
  have hrδ : r < δ := Int.emod_lt_of_pos (pi v z) hδpos
  have hrM : r < (M : ℤ) := lt_of_lt_of_le hrδ hMge
  have hmbound : m ≤ -(N0 : ℤ) := by
    have h1 : δ * m ≤ pi v z := by linarith [hr0]
    have h2 : δ * m ≤ -(N0 : ℤ) * δ := by rw [hτdef] at hz; linarith
    nlinarith [hδpos]
  set n : ℤ := -m with hndef
  have hnN0 : (N0 : ℤ) ≤ n := by rw [hndef]; linarith [hmbound]
  set off : ℕ := (n - N0).toNat with hoffdef
  have hoffcast : (off : ℤ) = n - N0 := Int.toNat_of_nonneg (by linarith [hnN0])
  have hnoff : n = ((N0 + off : ℕ) : ℤ) := by push_cast; linarith [hoffcast]
  set w : ℤ × ℤ := z - n • d with hwdef
  have hwpiv : pi v w = r := by
    have e1 : pi v w = pi v z - n * pi v d := by rw [hwdef, pi_sub, pi_smul]
    have hpivd : pi v d = -δ := by rw [hδdef]; ring
    have e5 : pi v z - n * pi v d = pi v z - m * δ := by rw [hpivd, hndef]; ring
    have e6 : m * δ = δ * m := mul_comm m δ
    rw [e1, e5]
    linarith [hsplit, e6]
  have hwpiv' : det v w = r := hwpiv
  have hwdecomp : w = (det w u) • v + r • u := by
    have h0 := eq_smul_add_smul hvu w
    rwa [hwpiv'] at h0
  have hperY : (k : ℤ) • v ∈ Per (Y off) := hΩper (Y off) (hYmem off)
  have hperGT : (k : ℤ) • v ∈ Per (fun w : ℤ × ℤ => G (w + ((N0 + off : ℕ) : ℤ) • d)) :=
    mem_Per_T_of_mem_Per (((N0 + off : ℕ) : ℤ) • d) hper
  have hagree0 : ∀ s' : ℤ, 0 ≤ s' → s' < (k : ℤ) →
      Y off (r • u + s' • v) = G (r • u + s' • v + ((N0 + off : ℕ) : ℤ) • d) := by
    intro s' hs'0 hs'k
    have hmemB : s' • v + r • u ∈ B := by
      rw [hBdef, Finset.mem_image]
      exact ⟨(s', r), Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ⟨hs'0, hs'k⟩,
        Finset.mem_Ico.mpr ⟨hr0, hrM⟩⟩, rfl⟩
    have hmemB2 : s' • v + r • u ∈ B2 := by rw [hB2def]; exact Finset.mem_union_left _ hmemB
    have h := hYspec off _ hmemB2
    rwa [add_comm (r • u) (s' • v)]
  have hrowfull := eq_of_period_agree_consecutive hk hperY hperGT hagree0
  have hreach0 := hrowfull (det w u)
  have hswap : r • u + (det w u) • v = w := (add_comm (r • u) ((det w u) • v)).trans hwdecomp.symm
  rw [hswap] at hreach0
  -- `hreach0 : Y off w = G (w + (N0 + off) • d)`
  have hzeq : w + ((N0 + off : ℕ) : ℤ) • d = z := by
    rw [hwdef, ← hnoff]; module
  rw [hzeq] at hreach0
  -- `hreach0 : Y off w = G z`
  have hYoffw : Y off w = Gd z := by
    rw [hYchain off, hGddef]
    show Y 0 (w + (off : ℤ) • d) = Y 0 (z + (-(N0 : ℤ)) • d)
    congr 1
    rw [hwdef, hoffcast]
    module
  exact hreach0.symm.trans hYoffw

/-! ### Theorem 8.12 -/

/-- Transporting `FullyPeriodicOnWith` along a pointwise-equal configuration on `U`: the shift
vectors `h, h'` and the "stays in `U`" clauses carry over unchanged, and the two value equalities
follow by chasing `heq` at both `z` and `z + h` (resp. `z + h'`), both of which lie in `U`. -/
private theorem fullyPeriodicOnWith_of_eqOn {p : ℕ} {G G' : Config (ZMod p)} {U : Set (ℤ × ℤ)}
    {h h' : ℤ × ℤ} (hfp : FullyPeriodicOnWith G U h h') (heq : ∀ z ∈ U, G z = G' z) :
    FullyPeriodicOnWith G' U h h' := by
  obtain ⟨hdet, hUh, hUh', hGh, hGh'⟩ := hfp
  refine ⟨hdet, hUh, hUh', fun z hz => ?_, fun z hz => ?_⟩
  · rw [← heq _ (hUh z hz), hGh z hz, heq z hz]
  · rw [← heq _ (hUh' z hz), hGh' z hz, heq z hz]

/-- Transporting `FullyPeriodicOn` along a pointwise-equal configuration on `U`. -/
private theorem fullyPeriodicOn_of_eqOn {p : ℕ} {G G' : Config (ZMod p)} {U : Set (ℤ × ℤ)}
    (hfp : FullyPeriodicOn G U) (heq : ∀ z ∈ U, G z = G' z) : FullyPeriodicOn G' U := by
  obtain ⟨h, h', hfp⟩ := hfp
  exact ⟨h, h', fullyPeriodicOnWith_of_eqOn hfp heq⟩

namespace FirstHalfPlane

variable {p n : ℕ} (D : FirstHalfPlane p n)

/-- **Theorem 8.12, assembled over all of `O` at once.**  Given a normalised `D` and a family `V`
already correct off `O`, produce a family correct everywhere.  Strong induction on `O` (via
`Finset.strongInductionOn`): if `O = ∅` the given family already works; otherwise Lemma 8.15
(`exists_available_direction`) picks `b ∈ O`, Proposition 8.14 and Lemma 8.16 build `Vᵢ`'s
replacement `V_b` for `b`, and the family with `b` patched in is correct off `O.erase b`, a
strictly smaller finset, so the induction hypothesis finishes it. -/
private theorem exists_family_half_plane [Fact p.Prime] (hnorm : D.Normalised)
    (hlow : LowConvexComplexity D.zeta) :
    ∀ O : Finset (Fin n), ∀ V : Fin n → Set (ℤ × ℤ),
      (∀ j ∉ O, ∃ t : ℤ, V j = latHalfPlane (!D.eps j) (D.v j) t ∧
        FullyPeriodicOn (D.G j) (V j) ∧ Disjoint (V j) (D.U j)) →
      ∃ V' : Fin n → Set (ℤ × ℤ), ∀ j : Fin n, ∃ t : ℤ, V' j = latHalfPlane (!D.eps j) (D.v j) t ∧
        FullyPeriodicOn (D.G j) (V' j) ∧ Disjoint (V' j) (D.U j) := by
  intro O
  induction O using Finset.strongInductionOn with
  | _ O ih =>
    intro V hV
    rcases O.eq_empty_or_nonempty with hOe | hOne
    · exact ⟨V, by rw [hOe] at hV; simpa using hV⟩
    · obtain ⟨b, c, d, hbO, hcb, hdne, hfix, hneg, hsafe⟩ :=
        D.exists_available_direction hnorm V O hOne
          (fun j hj => let ⟨t, h1, h2, _⟩ := hV j hj; ⟨t, h1, h2⟩)
      have hbc : b ≠ c := hcb.symm
      have hlimdp : ∀ Gb ∈ subseqLimits (D.G b) d, DoublyPeriodic Gb :=
        fun Gb hGb => D.doublyPeriodic_of_mem_subseqLimits hlow hbc hdne hfix hneg hsafe hGb
      have hepsb : D.eps b = true := hnorm b
      have hnegpi : pi (D.v b) d < 0 := by
        have h := hneg
        rw [hepsb] at h
        simpa [piE] using h
      have hd0 : 0 < -(pi (D.v b) d) := by linarith
      obtain ⟨u, hvu⟩ := (D.primitive b).exists_dual
      have hkpos : 0 < D.k b := D.k_pos b
      have hper : ((D.k b : ℤ) • D.v b) ∈ Per (D.G b) := D.period b
      obtain ⟨τ, Gd, hGddp, hagree⟩ := exists_doublyPeriodic_agree hvu hkpos hper hd0 hlimdp
      set t' : ℤ := -(min τ (D.t b - 1)) with ht'def
      set Vb : Set (ℤ × ℤ) := latHalfPlane (!D.eps b) (D.v b) t' with hVbdef
      have hVbHP : IsHalfPlane Vb :=
        isHalfPlane_latHalfPlane (D.primitive b).ne_zero (!D.eps b) t'
      have heqz : ∀ z ∈ Vb, Gd z = D.G b z := by
        intro z hz
        have hzmem : t' ≤ piE (!D.eps b) (D.v b) z := hz
        have hflip : piE (!D.eps b) (D.v b) z = -(pi (D.v b) z) := by rw [hepsb]; rfl
        rw [hflip, ht'def] at hzmem
        have hpiz : pi (D.v b) z ≤ min τ (D.t b - 1) := by omega
        exact (hagree z (le_trans hpiz (min_le_left _ _))).symm
      have hVbfp : FullyPeriodicOn (D.G b) Vb :=
        fullyPeriodicOn_of_eqOn (hGddp.fullyPeriodicOn hVbHP) heqz
      have hVbdisj : Disjoint Vb (D.U b) := by
        have h1 : min τ (D.t b - 1) ≤ D.t b - 1 := min_le_right _ _
        have hlt : -(D.t b) < t' := by rw [ht'def]; omega
        exact (disjoint_latHalfPlane (v := D.v b) (ε := D.eps b) hlt).symm
      set V2 : Fin n → Set (ℤ × ℤ) := fun j => if j = b then Vb else V j with hV2def
      have hV2 : ∀ j ∉ O.erase b, ∃ t : ℤ, V2 j = latHalfPlane (!D.eps j) (D.v j) t ∧
          FullyPeriodicOn (D.G j) (V2 j) ∧ Disjoint (V2 j) (D.U j) := by
        intro j hj
        by_cases hjb : j = b
        · subst hjb
          refine ⟨t', ?_, ?_, ?_⟩
          · simp [hV2def, hVbdef]
          · simpa [hV2def] using hVbfp
          · simpa [hV2def] using hVbdisj
        · have hjO : j ∉ O := fun hjO' => hj (Finset.mem_erase.mpr ⟨hjb, hjO'⟩)
          obtain ⟨t, h1, h2, h3⟩ := hV j hjO
          refine ⟨t, ?_, ?_, ?_⟩
          · simpa [hV2def, hjb] using h1
          · simpa [hV2def, hjb] using h2
          · simpa [hV2def, hjb] using h3
      exact ih (O.erase b) (Finset.erase_ssubset hbO) V2 hV2

/-- **Theorem 8.12 (The second half-plane) = Theorem 8.1(ii).**  In the notation of
Corollary 8.10, for every `i` there is a half-plane `Vᵢ` with `Vᵢ ∩ Uᵢ = ∅` such that `Gᵢ|Vᵢ`
is fully periodic.

Reduce to a normalised copy `D'` via `exists_normalised` (its `G` and `U` are literally those of
`D`), run `exists_family_half_plane` starting from `O := Finset.univ` (vacuously true off `O`) to
resolve *every* index at once, and read off the answer at `i`. -/
theorem exists_second_half_plane [Fact p.Prime] (hlow : LowConvexComplexity D.zeta) (i : Fin n) :
    ∃ V : Set (ℤ × ℤ), IsHalfPlane V ∧ Disjoint V (D.U i) ∧ FullyPeriodicOn (D.G i) V := by
  classical
  obtain ⟨D', hD'norm, hD'zeta, hD'G, hD'U⟩ := D.exists_normalised
  have hlow' : LowConvexComplexity D'.zeta := hD'zeta ▸ hlow
  obtain ⟨V', hV'⟩ := D'.exists_family_half_plane hD'norm hlow' Finset.univ
    (fun _ => (∅ : Set (ℤ × ℤ))) (fun j hj => absurd (Finset.mem_univ j) hj)
  obtain ⟨t, hVeq, hfp, hdisj⟩ := hV' i
  refine ⟨V' i, ?_, ?_, ?_⟩
  · rw [hVeq]; exact isHalfPlane_latHalfPlane (D'.primitive i).ne_zero (!D'.eps i) t
  · rw [← hD'U i]; exact hdisj
  · rw [← congrFun hD'G i]; exact hfp

end FirstHalfPlane

end Nivat
