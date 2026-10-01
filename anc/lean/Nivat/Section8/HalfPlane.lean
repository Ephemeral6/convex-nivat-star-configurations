/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.MainTheorem
import Mathlib.Analysis.Convex.Topology

/-!
# §8.1. Half-planes, regions and full periodicity

Formalisation of §8.1 of *The Convex Nivat Conjecture* (Pan).

A *half-plane* is a set `{z ∈ ℤ² : ⟨z, n⟩ > c}` or `{z ∈ ℤ² : ⟨z, n⟩ ≥ c}` with `n ∈ ℝ² \ {0}`.
A *lattice-convex region* is `R = C ∩ ℤ²` for a closed convex `C ⊆ ℝ²`; its recession cone is
`K_R = {w : C_R + w ⊆ C_R}`.  A field is *fully periodic* on `U` if two `ℝ`-independent lattice
vectors both preserve `U` and act trivially on `G|_U`.  Lemma 8.2 says that a fully periodic
field on such a set extends to a globally doubly periodic field.

## Main definitions

* `Nivat.IsHalfPlane`, `Nivat.latHalfPlane` — half-planes, and the rational ones `{ε π_v ≥ t}`.
* `Nivat.IsLatticeConvexRegion`, `Nivat.convHullOf`, `Nivat.recCone` — regions, `C_R`, `K_R`.
* `Nivat.FullyPeriodicOnWith`, `Nivat.FullyPeriodicOn` — full periodicity ([5, Definition 2.1]).

## Main results

* `Nivat.exists_global_extension` — **Lemma 8.2 (Global extension)**.

## Status

Complete; no `sorry`.
-/

namespace Nivat

open scoped Pointwise

variable {α : Type*}

/-! ### Half-planes -/

/-- The real linear form `⟨z, n⟩` on lattice points.  Paper §8.1. -/
def inner2 (n : ℝ × ℝ) (z : ℤ × ℤ) : ℝ := (z.1 : ℝ) * n.1 + (z.2 : ℝ) * n.2

theorem inner2_add (n : ℝ × ℝ) (z w : ℤ × ℤ) :
    inner2 n (z + w) = inner2 n z + inner2 n w := by
  simp only [inner2, Prod.fst_add, Prod.snd_add, Int.cast_add]
  ring

/-- The half-plane with normal `n` and threshold `c`; `strict` selects `>` over `≥`.
Paper §8.1. -/
def halfPlane (n : ℝ × ℝ) (c : ℝ) (strict : Bool) : Set (ℤ × ℤ) :=
  if strict then {z | c < inner2 n z} else {z | c ≤ inner2 n z}

/-- `H` is a half-plane.  Paper §8.1. -/
def IsHalfPlane (H : Set (ℤ × ℤ)) : Prop :=
  ∃ (n : ℝ × ℝ) (c : ℝ) (b : Bool), n ≠ 0 ∧ H = halfPlane n c b

/-- `ε π_v`, the signed linear form cutting out the rational half-planes of §8, with
`ε = true` for `+`. -/
def piE (ε : Bool) (v : ℤ × ℤ) (z : ℤ × ℤ) : ℤ := if ε then pi v z else -pi v z

/-- The real version of `ε π_v`. -/
def piER (ε : Bool) (v : ℤ × ℤ) (y : ℝ × ℝ) : ℝ := if ε then piR v y else -piR v y

@[simp] theorem piER_toReal (ε : Bool) (v z : ℤ × ℤ) :
    piER ε v (toReal z) = (piE ε v z : ℝ) := by
  cases ε <;> simp [piER, piE]

/-- The rational half-plane `{z : ε π_v z ≥ t}`.  Paper §8.3, §8.4. -/
def latHalfPlane (ε : Bool) (v : ℤ × ℤ) (t : ℤ) : Set (ℤ × ℤ) := {z | t ≤ piE ε v z}

theorem isHalfPlane_latHalfPlane {v : ℤ × ℤ} (hv : v ≠ 0) (ε : Bool) (t : ℤ) :
    IsHalfPlane (latHalfPlane ε v t) := by
  refine ⟨if ε then (-(v.2 : ℝ), (v.1 : ℝ)) else ((v.2 : ℝ), -(v.1 : ℝ)), (t : ℝ), false, ?_, ?_⟩
  · have hv' : v.1 ≠ 0 ∨ v.2 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv (Prod.ext hcon.1 hcon.2)
    cases ε <;> simp only [if_true, ne_eq, Prod.mk_eq_zero, not_and, neg_eq_zero] <;>
      intro h <;> rcases hv' with hv1 | hv2 <;>
      simp_all [Int.cast_eq_zero]
  · ext z
    simp only [latHalfPlane, halfPlane, Set.mem_ofPred_eq]
    constructor <;> intro h
    · cases ε with
      | true =>
        show (t : ℝ) ≤ inner2 (-(v.2 : ℝ), (v.1 : ℝ)) z
        have : inner2 (-(v.2 : ℝ), (v.1 : ℝ)) z = (piE true v z : ℝ) := by
          rw [← piER_toReal]; simp [inner2, piER, piR, toReal]; ring
        rw [this]; exact_mod_cast h
      | false =>
        show (t : ℝ) ≤ inner2 ((v.2 : ℝ), -(v.1 : ℝ)) z
        have : inner2 ((v.2 : ℝ), -(v.1 : ℝ)) z = (piE false v z : ℝ) := by
          rw [← piER_toReal]; simp [inner2, piER, piR, toReal]; ring
        rw [this]; exact_mod_cast h
    · cases ε with
      | true =>
        have h' : (t : ℝ) ≤ inner2 (-(v.2 : ℝ), (v.1 : ℝ)) z := h
        have heq : inner2 (-(v.2 : ℝ), (v.1 : ℝ)) z = (piE true v z : ℝ) := by
          rw [← piER_toReal]; simp [inner2, piER, piR, toReal]; ring
        rw [heq] at h'
        exact_mod_cast h'
      | false =>
        have h' : (t : ℝ) ≤ inner2 ((v.2 : ℝ), -(v.1 : ℝ)) z := h
        have heq : inner2 ((v.2 : ℝ), -(v.1 : ℝ)) z = (piE false v z : ℝ) := by
          rw [← piER_toReal]; simp [inner2, piER, piR, toReal]; ring
        rw [heq] at h'
        exact_mod_cast h'

/-- `{ε π_v ≥ t}` and `{-ε π_v ≥ t'}` are disjoint as soon as the thresholds leave a gap:
`0 < t + t'`, i.e. `-t < t'`.  Paper §8.4, the construction of `V_b`.

(The hypothesis must be stated with this direction: the opposite inequality `t' < -t` would
make the statement false in general, e.g. `v = 0`, `t = -5`, `t' = -3` gives `piE ε v z = 0`
for every `z`, so both half-planes equal `Set.univ` and are not disjoint.) -/
theorem disjoint_latHalfPlane {v : ℤ × ℤ} {ε : Bool} {t t' : ℤ} (h : -t < t') :
    Disjoint (latHalfPlane ε v t) (latHalfPlane (!ε) v t') := by
  rw [Set.disjoint_left]
  intro z hz hz'
  simp only [latHalfPlane, Set.mem_ofPred_eq] at hz hz'
  have hflip : piE (!ε) v z = -piE ε v z := by
    cases ε <;> simp [piE]
  rw [hflip] at hz'
  omega

/-- If `⟨g, n⟩ ≥ 0` then `H + g ⊆ H`.  Paper §8.1. -/
theorem halfPlane_add_subset {n : ℝ × ℝ} {c : ℝ} {b : Bool} {g : ℤ × ℤ}
    (hg : 0 ≤ inner2 n g) : (fun z => z + g) '' halfPlane n c b ⊆ halfPlane n c b := by
  rintro _ ⟨z, hz, rfl⟩
  cases b with
  | true =>
    rw [halfPlane, if_pos rfl] at hz ⊢
    simp only [Set.mem_ofPred_eq] at hz ⊢
    rw [inner2_add]; linarith
  | false =>
    rw [halfPlane, if_neg (by decide)] at hz ⊢
    simp only [Set.mem_ofPred_eq] at hz ⊢
    rw [inner2_add]; linarith

/-- `inner2` scales linearly under integer scalar multiples. -/
theorem inner2_zsmul (n : ℝ × ℝ) (k : ℤ) (z : ℤ × ℤ) :
    inner2 n (k • z) = (k : ℝ) * inner2 n z := by
  simp only [inner2, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  push_cast
  ring

/-- If `⟨g, n⟩ > 0` then `⋃_N (H - N g) = ℤ²`: every lattice point is translated into `H` by a
large multiple of `g`.  Paper §8.1. -/
theorem exists_add_nsmul_mem_halfPlane {n : ℝ × ℝ} {c : ℝ} {b : Bool} {g : ℤ × ℤ}
    (hg : 0 < inner2 n g) (hne : (halfPlane n c b).Nonempty) (z : ℤ × ℤ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → z + (N : ℤ) • g ∈ halfPlane n c b := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((c - inner2 n z) / inner2 n g)
  refine ⟨N₀, fun N hN => ?_⟩
  have hstep : (c - inner2 n z) / inner2 n g < (N : ℝ) :=
    hN₀.trans_le (by exact_mod_cast hN)
  have hlt : c - inner2 n z < (N : ℝ) * inner2 n g := by
    rwa [div_lt_iff₀ hg] at hstep
  cases b with
  | true =>
    rw [halfPlane, if_pos rfl]
    simp only [Set.mem_ofPred_eq, inner2_add, inner2_zsmul]
    push_cast
    linarith
  | false =>
    rw [halfPlane, if_neg (by decide)]
    simp only [Set.mem_ofPred_eq, inner2_add, inner2_zsmul]
    push_cast
    linarith

/-! ### Lattice-convex regions -/

/-- `R ⊆ ℤ²` is a *lattice-convex region* if `R = C ∩ ℤ²` for a closed convex `C ⊆ ℝ²`.
Paper §8.1. -/
def IsLatticeConvexRegion (R : Set (ℤ × ℤ)) : Prop :=
  ∃ C : Set (ℝ × ℝ), Convex ℝ C ∧ IsClosed C ∧ R = toReal ⁻¹' C

/-- `C_R = Conv(R)`, the closed convex hull of a region.  Paper §8.1. -/
def convHullOf (R : Set (ℤ × ℤ)) : Set (ℝ × ℝ) := closure (convexHull ℝ (toReal '' R))

/-- One still has `R = C_R ∩ ℤ²` for a lattice-convex region, since `R ⊆ C_R ⊆ C`.
Paper §8.1. -/
theorem eq_preimage_convHullOf {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R) :
    R = toReal ⁻¹' convHullOf R := by
  obtain ⟨C, hCconv, hCclosed, hReq⟩ := hR
  have hsub : toReal '' R ⊆ C := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hReq] at hz
    exact hz
  have hconvHullOf_sub : convHullOf R ⊆ C := by
    calc convHullOf R = closure (convexHull ℝ (toReal '' R)) := rfl
    _ ⊆ closure C := closure_mono (convexHull_min hsub hCconv)
    _ = C := hCclosed.closure_eq
  ext z
  constructor
  · intro hz
    show toReal z ∈ convHullOf R
    exact subset_closure (subset_convexHull ℝ _ ⟨z, hz, rfl⟩)
  · intro hz
    rw [hReq]
    exact hconvHullOf_sub hz

/-- The recession cone `K_R = {w ∈ ℝ² : C_R + w ⊆ C_R}`, a closed convex cone.
Paper §8.1. -/
def recCone (R : Set (ℤ × ℤ)) : Set (ℝ × ℝ) := {w | ∀ x ∈ convHullOf R, x + w ∈ convHullOf R}

theorem convex_recCone (R : Set (ℤ × ℤ)) : Convex ℝ (recCone R) := by
  have hconv : Convex ℝ (convHullOf R) := (convex_convexHull ℝ _).closure
  intro w₁ hw₁ w₂ hw₂ a b ha hb hab x hx
  have h1 : x + w₁ ∈ convHullOf R := hw₁ x hx
  have h2 : x + w₂ ∈ convHullOf R := hw₂ x hx
  have hcomb : a • (x + w₁) + b • (x + w₂) ∈ convHullOf R := hconv h1 h2 ha hb hab
  have hx' : a • x + b • x = x := by rw [← add_smul, hab, one_smul]
  have heq : a • (x + w₁) + b • (x + w₂) = x + (a • w₁ + b • w₂) := by
    rw [smul_add, smul_add, add_add_add_comm, hx']
  rwa [heq] at hcomb

/-- If `R + h ⊆ R` for an integer vector `h`, then `h ∈ K_R`.  Paper §8.1. -/
theorem toReal_mem_recCone {R : Set (ℤ × ℤ)} {h : ℤ × ℤ}
    (hh : ∀ z ∈ R, z + h ∈ R) : toReal h ∈ recCone R := by
  set S : Set (ℝ × ℝ) := toReal '' R with hS
  have hSh_sub : (fun x => toReal h +ᵥ x) '' S ⊆ S := by
    rintro _ ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z + h, hh z hz, by simp only [vadd_eq_add]; rw [toReal_add]; abel⟩
  have himg := (AffineEquiv.constVAdd ℝ (ℝ × ℝ) (toReal h)).toAffineMap.image_convexHull S
  have hbase : (fun x => toReal h +ᵥ x) '' convexHull ℝ S ⊆ convexHull ℝ S := by
    rw [show (fun x => toReal h +ᵥ x) '' convexHull ℝ S
        = convexHull ℝ ((fun x => toReal h +ᵥ x) '' S) from himg]
    exact convexHull_mono hSh_sub
  have hcont : Continuous (fun x : ℝ × ℝ => toReal h +ᵥ x) := by
    simp only [vadd_eq_add]; exact continuous_const.add continuous_id
  have hmaps0 : Set.MapsTo (fun x => toReal h +ᵥ x) (convexHull ℝ S) (convexHull ℝ S) :=
    fun x hx => hbase ⟨x, hx, rfl⟩
  have hmaps : Set.MapsTo (fun x => toReal h +ᵥ x) (closure (convexHull ℝ S))
      (closure (convexHull ℝ S)) := hmaps0.closure hcont
  intro x hx
  have hthis : toReal h +ᵥ x ∈ closure (convexHull ℝ S) := hmaps hx
  rwa [vadd_eq_add, add_comm] at hthis

/-- A cone *spans the plane*, i.e. `dim K = 2`, if it contains two linearly independent
vectors.  Paper §8.1, §8.3. -/
def SpansPlane (K : Set (ℝ × ℝ)) : Prop :=
  ∃ x ∈ K, ∃ y ∈ K, x.1 * y.2 - x.2 * y.1 ≠ 0

/-- The real line `ℝ v` through a lattice direction.  Paper Proposition 8.9. -/
def lineR (v : ℤ × ℤ) : Set (ℝ × ℝ) := {y | ∃ c : ℝ, y = c • toReal v}

/-! ### Full periodicity -/

/-- `G` is *fully periodic* on `U` with the vectors `h, h'` ([5, Definition 2.1]): the two
vectors are `ℝ`-linearly independent, both preserve `U`, and both act trivially on `G|_U`.
Paper §8.1. -/
def FullyPeriodicOnWith (G : Config α) (U : Set (ℤ × ℤ)) (h h' : ℤ × ℤ) : Prop :=
  det h h' ≠ 0 ∧ (∀ z ∈ U, z + h ∈ U) ∧ (∀ z ∈ U, z + h' ∈ U) ∧
    (∀ z ∈ U, G (z + h) = G z) ∧ (∀ z ∈ U, G (z + h') = G z)

/-- `G` is fully periodic on `U`.  Paper §8.1. -/
def FullyPeriodicOn (G : Config α) (U : Set (ℤ × ℤ)) : Prop :=
  ∃ h h' : ℤ × ℤ, FullyPeriodicOnWith G U h h'

/-- `inner2 n (-z) = -inner2 n z`. -/
theorem inner2_neg (n : ℝ × ℝ) (z : ℤ × ℤ) : inner2 n (-z) = -inner2 n z := by
  simp only [inner2, Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
  ring

/-- The restriction of a doubly periodic field to a half-plane is fully periodic: take two
independent vectors of its period lattice pointing into the half-plane.  Paper §8.1. -/
theorem DoublyPeriodic.fullyPeriodicOn {G : Config α} (hG : DoublyPeriodic G)
    {U : Set (ℤ × ℤ)} (hU : IsHalfPlane U) : FullyPeriodicOn G U := by
  obtain ⟨n, c, b, _hn, hUeq⟩ := hU
  obtain ⟨u, hu, v, hv, hdet⟩ := hG
  set h₁ : ℤ × ℤ := if 0 ≤ inner2 n u then u else -u with hh₁def
  set h₂ : ℤ × ℤ := if 0 ≤ inner2 n v then v else -v with hh₂def
  have hh₁mem : h₁ ∈ Per G := by
    rw [hh₁def]; split_ifs
    · exact hu
    · exact (Per G).neg_mem hu
  have hh₂mem : h₂ ∈ Per G := by
    rw [hh₂def]; split_ifs
    · exact hv
    · exact (Per G).neg_mem hv
  have hh₁pos : 0 ≤ inner2 n h₁ := by
    rw [hh₁def]; split_ifs with h
    · exact h
    · rw [inner2_neg]; linarith
  have hh₂pos : 0 ≤ inner2 n h₂ := by
    rw [hh₂def]; split_ifs with h
    · exact h
    · rw [inner2_neg]; linarith
  have hh₁h₂det : det h₁ h₂ ≠ 0 := by
    rw [hh₁def, hh₂def]
    split_ifs
    · exact hdet
    · have : det u (-v) = -det u v := by simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
      rw [this]; exact neg_ne_zero.mpr hdet
    · have : det (-u) v = -det u v := by simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
      rw [this]; exact neg_ne_zero.mpr hdet
    · have : det (-u) (-v) = det u v := by simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
      rw [this]; exact hdet
  refine ⟨h₁, h₂, hh₁h₂det, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hz' : z ∈ halfPlane n c b := hUeq ▸ hz
    have := halfPlane_add_subset hh₁pos ⟨z, hz', rfl⟩
    rwa [hUeq]
  · intro z hz
    have hz' : z ∈ halfPlane n c b := hUeq ▸ hz
    have := halfPlane_add_subset hh₂pos ⟨z, hz', rfl⟩
    rwa [hUeq]
  · intro z _
    exact Per.apply hh₁mem z
  · intro z _
    exact Per.apply hh₂mem z

/-- `toReal` scales linearly under integer scalar multiples. -/
theorem toReal_zsmul (k : ℤ) (z : ℤ × ℤ) : toReal (k • z) = (k : ℝ) • toReal z := by
  apply Prod.ext <;> simp [toReal, smul_eq_mul]

/-- `K_R` is closed under addition. -/
theorem add_mem_recCone {R : Set (ℤ × ℤ)} {x y : ℝ × ℝ}
    (hx : x ∈ recCone R) (hy : y ∈ recCone R) : x + y ∈ recCone R := by
  intro p hp
  have h1 : p + x ∈ convHullOf R := hx p hp
  have h2 : (p + x) + y ∈ convHullOf R := hy _ h1
  rwa [add_assoc] at h2

/-- `K_R` is closed under `ℕ`-scaling. -/
theorem nsmul_mem_recCone {R : Set (ℤ × ℤ)} (k : ℕ) {x : ℝ × ℝ}
    (hx : x ∈ recCone R) : k • x ∈ recCone R := by
  induction k with
  | zero => intro p hp; simpa using hp
  | succ k ih =>
    have hstep := add_mem_recCone ih hx
    rw [succ_nsmul]
    exact hstep

/-- `K_R` is closed under nonnegative real scaling: it is a cone. -/
theorem smul_mem_recCone {R : Set (ℤ × ℤ)} {x : ℝ × ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hx : x ∈ recCone R) : t • x ∈ recCone R := by
  have hconv := convex_recCone R
  set k : ℕ := ⌊t⌋₊ with hkdef
  have hk_le : (k : ℝ) ≤ t := Nat.floor_le ht
  have hk_lt : t < (k : ℝ) + 1 := Nat.lt_floor_add_one t
  set r : ℝ := t - k with hrdef
  have hr0 : 0 ≤ r := by simp only [hrdef]; linarith
  have hr1 : r ≤ 1 := by simp only [hrdef]; linarith
  have h1mr : 0 ≤ 1 - r := by linarith
  have hk_mem : (k : ℝ) • x ∈ recCone R := by
    rw [Nat.cast_smul_eq_nsmul ℝ]
    exact nsmul_mem_recCone k hx
  have hk1_mem : ((k : ℝ) + 1) • x ∈ recCone R := by
    have hh := nsmul_mem_recCone (k + 1) hx
    rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Nat.cast_smul_eq_nsmul ℝ]
    exact hh
  have hcomb := hconv hk_mem hk1_mem h1mr hr0 (by ring)
  have heq : (1 - r) • ((k : ℝ) • x) + r • (((k : ℝ) + 1) • x) = t • x := by
    rw [smul_smul, smul_smul, ← add_smul]
    congr 1
    rw [hrdef]; ring
  rwa [heq] at hcomb

/-- **Lemma 8.2**, the cone statement for a region: `g = h + h'` lies in the interior of `K_R`,
which therefore spans the plane. -/
theorem mem_interior_recCone {G : Config α} {R : Set (ℤ × ℤ)}
    (_hR : IsLatticeConvexRegion R) (_hne : R.Nonempty)
    {h h' : ℤ × ℤ} (hfp : FullyPeriodicOnWith G R h h') :
    toReal h ∈ recCone R ∧ toReal h' ∈ recCone R ∧
      toReal (h + h') ∈ interior (recCone R) ∧ SpansPlane (recCone R) := by
  obtain ⟨hdet, hRh, hRh', _, _⟩ := hfp
  have hmemh : toReal h ∈ recCone R := toReal_mem_recCone hRh
  have hmemh' : toReal h' ∈ recCone R := toReal_mem_recCone hRh'
  set v : ℝ × ℝ := toReal h with hvdef
  set w : ℝ × ℝ := toReal h' with hwdef
  set D : ℝ := v.1 * w.2 - v.2 * w.1 with hDdef
  have hDne : D ≠ 0 := by
    have hcast : ((det h h' : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hdet
    simp only [det, hDdef, hvdef, hwdef, toReal] at hcast ⊢
    push_cast at hcast
    exact hcast
  -- The closed sector spanned by `v` and `w` lies in `K_R`.
  have hsector_mem : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → a • v + b • w ∈ recCone R := by
    intro a b ha hb
    exact add_mem_recCone (smul_mem_recCone ha hmemh) (smul_mem_recCone hb hmemh')
  -- Coordinates with respect to the basis `(v, w)`.
  set av : ℝ × ℝ → ℝ := fun p => (p.1 * w.2 - p.2 * w.1) / D with havdef
  set bv : ℝ × ℝ → ℝ := fun p => (v.1 * p.2 - v.2 * p.1) / D with hbvdef
  have hrecon : ∀ p : ℝ × ℝ, av p • v + bv p • w = p := by
    intro p
    apply Prod.ext <;>
      · simp only [havdef, hbvdef, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
          smul_eq_mul]
        field_simp
        ring
  have hav_cont : Continuous av := by
    simp only [havdef]
    exact (((continuous_fst.mul continuous_const).sub
      (continuous_snd.mul continuous_const))).div_const D
  have hbv_cont : Continuous bv := by
    simp only [hbvdef]
    exact (((continuous_const.mul continuous_snd).sub
      (continuous_const.mul continuous_fst))).div_const D
  have have_vw : av (v + w) = 1 := by
    simp only [havdef, Prod.fst_add, Prod.snd_add]
    field_simp
    ring
  have hbv_vw : bv (v + w) = 1 := by
    simp only [hbvdef, Prod.fst_add, Prod.snd_add]
    field_simp
    ring
  set T : Set (ℝ × ℝ) := {p | 0 < av p ∧ 0 < bv p} with hTdef
  have hTopen : IsOpen T := by
    rw [hTdef]
    exact (isOpen_lt continuous_const hav_cont).inter (isOpen_lt continuous_const hbv_cont)
  have hTsub : T ⊆ recCone R := by
    intro p hp
    obtain ⟨hap, hbp⟩ := hp
    rw [← hrecon p]
    exact hsector_mem hap.le hbp.le
  have hmemT : v + w ∈ T := ⟨by rw [have_vw]; norm_num, by rw [hbv_vw]; norm_num⟩
  have hmem_interior : v + w ∈ interior (recCone R) := interior_maximal hTsub hTopen hmemT
  refine ⟨hmemh, hmemh', ?_, v, hmemh, w, hmemh', hDne⟩
  have : toReal (h + h') = v + w := by rw [hvdef, hwdef, toReal_add]
  rwa [this]

/-- `inner2` scales linearly under natural scalar multiples. -/
theorem inner2_nsmul (n : ℝ × ℝ) (k : ℕ) (z : ℤ × ℤ) :
    inner2 n (k • z) = (k : ℝ) * inner2 n z := by
  simp only [inner2, Prod.smul_fst, Prod.smul_snd]
  simp only [nsmul_eq_mul]
  push_cast
  ring

/-- If `R + g ⊆ R` for a non-empty half-plane `R` then `⟨g, n⟩ ≥ 0`: otherwise repeated addition
of `g` would eventually leave `R`.  Paper §8.4, step (★). -/
theorem inner2_nonneg_of_halfPlane_add_subset {n : ℝ × ℝ} {c : ℝ} {b : Bool}
    (hne : (halfPlane n c b).Nonempty) {g : ℤ × ℤ}
    (hgsub : ∀ z ∈ halfPlane n c b, z + g ∈ halfPlane n c b) : 0 ≤ inner2 n g := by
  by_contra hcon
  push Not at hcon
  obtain ⟨z0, hz0⟩ := hne
  have hiter : ∀ k : ℕ, z0 + k • g ∈ halfPlane n c b := by
    intro k
    induction k with
    | zero => simpa using hz0
    | succ k ih =>
      have hstep := hgsub _ ih
      rw [succ_nsmul, ← add_assoc]
      exact hstep
  obtain ⟨N, hN⟩ := exists_nat_gt ((inner2 n z0 - c) / (-(inner2 n g)))
  have hmemN := hiter N
  have hval : inner2 n (z0 + N • g) = inner2 n z0 + (N : ℝ) * inner2 n g := by
    rw [inner2_add, inner2_nsmul]
  have hcneg : 0 < -(inner2 n g) := by linarith
  have hlt : inner2 n z0 - c < (N : ℝ) * (-(inner2 n g)) := by
    rwa [div_lt_iff₀ hcneg] at hN
  cases b with
  | true =>
    rw [halfPlane, if_pos rfl] at hmemN
    simp only [Set.mem_ofPred_eq] at hmemN
    rw [hval] at hmemN
    nlinarith
  | false =>
    rw [halfPlane, if_neg (by decide)] at hmemN
    simp only [Set.mem_ofPred_eq] at hmemN
    rw [hval] at hmemN
    nlinarith

/-- **Lemma 8.2**, the cone statement for a half-plane: `⟨g, n⟩ > 0`. -/
theorem inner2_pos_of_fullyPeriodic {G : Config α} {n : ℝ × ℝ} {c : ℝ} {b : Bool}
    (hn : n ≠ 0) (hne : (halfPlane n c b).Nonempty)
    {h h' : ℤ × ℤ} (hfp : FullyPeriodicOnWith G (halfPlane n c b) h h') :
    0 < inner2 n (h + h') := by
  obtain ⟨hdet, hUh, hUh', _, _⟩ := hfp
  have hnh : 0 ≤ inner2 n h := inner2_nonneg_of_halfPlane_add_subset hne hUh
  have hnh' : 0 ≤ inner2 n h' := inner2_nonneg_of_halfPlane_add_subset hne hUh'
  have hnot_both : ¬ (inner2 n h = 0 ∧ inner2 n h' = 0) := by
    rintro ⟨e1, e2⟩
    simp only [inner2] at e1 e2
    have key1 : n.1 * ((h.1 : ℝ) * h'.2 - h.2 * h'.1) = 0 := by
      linear_combination h'.2 * e1 - h.2 * e2
    have key2 : n.2 * ((h.1 : ℝ) * h'.2 - h.2 * h'.1) = 0 := by
      linear_combination h.1 * e2 - h'.1 * e1
    have hn' : n.1 ≠ 0 ∨ n.2 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hn (Prod.ext hcon.1 hcon.2)
    have hzero : (h.1 : ℝ) * h'.2 - h.2 * h'.1 = 0 := by
      rcases hn' with hn1 | hn2
      · exact (mul_eq_zero.mp key1).resolve_left hn1
      · exact (mul_eq_zero.mp key2).resolve_left hn2
    apply hdet
    have : ((det h h' : ℤ) : ℝ) = 0 := by
      simp only [det]; push_cast; linarith [hzero]
    exact_mod_cast this
  rw [inner2_add]
  rcases lt_or_eq_of_le hnh with hpos | hzero
  · rcases lt_or_eq_of_le hnh' with hpos' | hzero'
    · linarith
    · linarith
  · rcases lt_or_eq_of_le hnh' with hpos' | hzero'
    · linarith
    · exact absurd ⟨hzero.symm, hzero'.symm⟩ hnot_both

/-- **Lemma 8.2 (Global extension).**  Let `R` be a lattice-convex region or a half-plane and
let `G` be fully periodic on `R` with vectors `h, h'`.  Put `g = h + h'`.  Then every `z` is
translated into `R` by all large multiples of `g`, and there is a doubly periodic `G'` with
`h, h' ∈ Per G'` and `G' = G` on `R`. -/
theorem exists_global_extension {G : Config α} {R : Set (ℤ × ℤ)}
    (hR : IsLatticeConvexRegion R ∨ IsHalfPlane R) (hne : R.Nonempty)
    {h h' : ℤ × ℤ} (hfp : FullyPeriodicOnWith G R h h') :
    (∀ z : ℤ × ℤ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → z + (N : ℤ) • (h + h') ∈ R) ∧
      ∃ G' : Config α, h ∈ Per G' ∧ h' ∈ Per G' ∧ DoublyPeriodic G' ∧ ∀ z ∈ R, G' z = G z := by
  obtain ⟨hdet, hRh, hRh', hGh, hGh'⟩ := hfp
  set g : ℤ × ℤ := h + h' with hgdef
  -- Part 1: every `z` is eventually translated into `R` by multiples of `g`.
  have hpart1 : ∀ z : ℤ × ℤ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → z + (N : ℤ) • g ∈ R := by
    rcases hR with hRconv | hRhalf
    · obtain ⟨_, _, hmemg, _⟩ :=
        mem_interior_recCone hRconv hne ⟨hdet, hRh, hRh', hGh, hGh'⟩
      obtain ⟨x0, hx0⟩ := hne
      have hx0' : toReal x0 ∈ convHullOf R :=
        subset_closure (subset_convexHull ℝ _ ⟨x0, hx0, rfl⟩)
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior (toReal g) hmemg
      intro z
      set d : ℝ := ‖toReal z - toReal x0‖ with hddef
      obtain ⟨N₁, hN₁⟩ := exists_nat_gt (d / ε)
      refine ⟨N₁ + 1, fun N hN => ?_⟩
      have hNpos : (0 : ℝ) < (N : ℝ) := by
        have : (0 : ℕ) < N := by omega
        exact_mod_cast this
      have hNgt : d / ε < (N : ℝ) := by
        have hlt : (N₁ : ℝ) < (N : ℝ) := by exact_mod_cast (show N₁ < N by omega)
        linarith
      have hdlt : d < ε * (N : ℝ) := by
        have := (div_lt_iff₀ hε).mp hNgt
        linarith [this]
      set v : ℝ × ℝ := toReal g + (N : ℝ)⁻¹ • (toReal z - toReal x0) with hvdef
      have hvball : v ∈ Metric.ball (toReal g) ε := by
        rw [Metric.mem_ball, hvdef, dist_eq_norm]
        have heq2 : toReal g + (N : ℝ)⁻¹ • (toReal z - toReal x0) - toReal g
            = (N : ℝ)⁻¹ • (toReal z - toReal x0) := by abel
        rw [heq2, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hNpos), ← hddef]
        rw [inv_mul_lt_iff₀ hNpos]
        linarith [hdlt]
      have hvrec : v ∈ recCone R := interior_subset (hball hvball)
      have hscaled : (N : ℝ) • v ∈ recCone R := smul_mem_recCone hNpos.le hvrec
      have hmemC : toReal x0 + (N : ℝ) • v ∈ convHullOf R := hscaled _ hx0'
      have heq : toReal x0 + (N : ℝ) • v = toReal (z + (N : ℤ) • g) := by
        have hrhs : toReal (z + (N : ℤ) • g) = toReal z + (N : ℝ) • toReal g := by
          rw [toReal_add, toReal_zsmul]
          norm_cast
        rw [hrhs, hvdef, smul_add, smul_smul, mul_inv_cancel₀ (ne_of_gt hNpos), one_smul]
        abel
      rw [eq_preimage_convHullOf hRconv]
      show toReal (z + (N : ℤ) • g) ∈ convHullOf R
      rw [← heq]
      exact hmemC
    · obtain ⟨n, c, b, hnz, hReq⟩ := hRhalf
      subst hReq
      have hg_pos : 0 < inner2 n g :=
        inner2_pos_of_fullyPeriodic hnz hne ⟨hdet, hRh, hRh', hGh, hGh'⟩
      exact fun z => exists_add_nsmul_mem_halfPlane hg_pos hne z
  -- Step 1: `g`-translates of points of `R` stay in `R` and are `G`-invariant.
  have hstepG : ∀ z ∈ R, z + g ∈ R ∧ G (z + g) = G z := by
    intro z hz
    have hz1 : z + h ∈ R := hRh z hz
    have hz1' : G (z + h) = G z := hGh z hz
    have hz2 : (z + h) + h' ∈ R := hRh' (z + h) hz1
    have hz2' : G ((z + h) + h') = G (z + h) := hGh' (z + h) hz1
    refine ⟨?_, ?_⟩
    · rwa [hgdef, ← add_assoc]
    · rw [hgdef, ← add_assoc, hz2', hz1']
  have hstepG_iter : ∀ (k : ℕ) {z : ℤ × ℤ}, z ∈ R →
      z + (k : ℤ) • g ∈ R ∧ G (z + (k : ℤ) • g) = G z := by
    intro k
    induction k with
    | zero =>
      intro z hz
      constructor
      · simpa using hz
      · simp
    | succ k ih =>
      intro z hz
      obtain ⟨ih1, ih2⟩ := ih hz
      obtain ⟨hstep1, hstep2⟩ := hstepG _ ih1
      have hcast : ((k + 1 : ℕ) : ℤ) • g = (k : ℤ) • g + g := by
        push_cast
        rw [add_zsmul, one_zsmul]
      constructor
      · rw [hcast, ← add_assoc]
        exact hstep1
      · rw [hcast, ← add_assoc, hstep2]
        exact ih2
  -- Well-definedness: `G (z + N g)` does not depend on the choice of valid `N`.
  have hkey : ∀ (z : ℤ × ℤ) (N N' : ℕ), z + (N : ℤ) • g ∈ R → z + (N' : ℤ) • g ∈ R →
      G (z + (N : ℤ) • g) = G (z + (N' : ℤ) • g) := by
    have hkey' : ∀ (z : ℤ × ℤ) (N N' : ℕ), N ≤ N' → z + (N : ℤ) • g ∈ R →
        G (z + (N : ℤ) • g) = G (z + (N' : ℤ) • g) := by
      intro z N N' hle hzN
      obtain ⟨k, hk⟩ := Nat.le.dest hle
      obtain ⟨_, hg2⟩ := hstepG_iter k hzN
      have heq : z + (N : ℤ) • g + (k : ℤ) • g = z + (N' : ℤ) • g := by
        have hcast : (N : ℤ) + (k : ℤ) = (N' : ℤ) := by exact_mod_cast hk
        rw [add_assoc, ← add_zsmul, hcast]
      have hg2' : G (z + (N' : ℤ) • g) = G (z + (N : ℤ) • g) := by rw [← heq]; exact hg2
      exact hg2'.symm
    intro z N N' hzN hzN'
    rcases le_total N N' with hle | hle
    · exact hkey' z N N' hle hzN
    · exact (hkey' z N' N hle hzN').symm
  -- Definition of `G'`.
  set N₀ : ℤ × ℤ → ℕ := fun z => (hpart1 z).choose with hN₀def
  have hN₀spec : ∀ z : ℤ × ℤ, z + (N₀ z : ℤ) • g ∈ R :=
    fun z => (hpart1 z).choose_spec (N₀ z) (le_refl _)
  set G' : Config α := fun z => G (z + (N₀ z : ℤ) • g) with hG'def
  have hPerh : h ∈ Per G' := by
    rw [mem_Per_iff]
    funext z
    rw [T_apply]
    show G' (z + h) = G' z
    set N : ℕ := N₀ z with hNdef
    have hzN : z + (N : ℤ) • g ∈ R := hN₀spec z
    have hzhN : z + h + (N : ℤ) • g ∈ R := by
      have hstep := hRh _ hzN
      rwa [show z + (N : ℤ) • g + h = z + h + (N : ℤ) • g by abel] at hstep
    have hGeq : G (z + (N : ℤ) • g + h) = G (z + (N : ℤ) • g) := hGh _ hzN
    show G (z + h + (N₀ (z + h) : ℤ) • g) = G (z + (N₀ z : ℤ) • g)
    have hL : G (z + h + (N₀ (z + h) : ℤ) • g) = G (z + h + (N : ℤ) • g) :=
      hkey (z + h) (N₀ (z + h)) N (hN₀spec (z + h)) hzhN
    rw [hL, show z + h + (N : ℤ) • g = z + (N : ℤ) • g + h by abel, hGeq]
  have hPerh' : h' ∈ Per G' := by
    rw [mem_Per_iff]
    funext z
    rw [T_apply]
    show G' (z + h') = G' z
    set N : ℕ := N₀ z with hNdef
    have hzN : z + (N : ℤ) • g ∈ R := hN₀spec z
    have hzhN : z + h' + (N : ℤ) • g ∈ R := by
      have hstep := hRh' _ hzN
      rwa [show z + (N : ℤ) • g + h' = z + h' + (N : ℤ) • g by abel] at hstep
    have hGeq : G (z + (N : ℤ) • g + h') = G (z + (N : ℤ) • g) := hGh' _ hzN
    show G (z + h' + (N₀ (z + h') : ℤ) • g) = G (z + (N₀ z : ℤ) • g)
    have hL : G (z + h' + (N₀ (z + h') : ℤ) • g) = G (z + h' + (N : ℤ) • g) :=
      hkey (z + h') (N₀ (z + h')) N (hN₀spec (z + h')) hzhN
    rw [hL, show z + h' + (N : ℤ) • g = z + (N : ℤ) • g + h' by abel, hGeq]
  refine ⟨hpart1, G', hPerh, hPerh', ⟨h, hPerh, h', hPerh', hdet⟩, ?_⟩
  intro z hz
  show G (z + (N₀ z : ℤ) • g) = G z
  have hz0 : z + ((0 : ℕ) : ℤ) • g ∈ R := by simpa using hz
  have hh := hkey z (N₀ z) 0 (hN₀spec z) hz0
  simpa using hh

/-- The global extension of `G|_H`, chosen once and for all.  Paper §8.4 writes this `G_j^H`. -/
noncomputable def globalExt (G : Config α) (R : Set (ℤ × ℤ))
    (hR : IsLatticeConvexRegion R ∨ IsHalfPlane R) (hne : R.Nonempty)
    {h h' : ℤ × ℤ} (hfp : FullyPeriodicOnWith G R h h') : Config α :=
  ((exists_global_extension hR hne hfp).2).choose

theorem globalExt_spec {G : Config α} {R : Set (ℤ × ℤ)}
    (hR : IsLatticeConvexRegion R ∨ IsHalfPlane R) (hne : R.Nonempty)
    {h h' : ℤ × ℤ} (hfp : FullyPeriodicOnWith G R h h') :
    DoublyPeriodic (globalExt G R hR hne hfp) ∧
      ∀ z ∈ R, globalExt G R hR hne hfp z = G z := by
  have := ((exists_global_extension hR hne hfp).2).choose_spec
  exact ⟨this.2.2.1, this.2.2.2⟩

end Nivat
