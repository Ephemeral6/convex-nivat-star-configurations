/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Section8.HalfPlane

/-!
# Planar closed convex cones: separation and classification

Convex-geometry facts about closed convex cones `K ⊆ ℝ²` that §8.3–§8.4 of *The Convex Nivat
Conjecture* (Pan) use for the recession cone `K = K_R` of Proposition 8.9 and for
the sector `K_O` of Lemma 8.16.  Everything here is stated for an abstract `K : Set (ℝ × ℝ)`;
the consumers instantiate `K := recCone R`.

## Main results

* `Nivat.exists_side_of_line_not_mem_interior_of_nonempty_interior` — if the line `ℝ v` misses
  the interior of a convex cone `K` with non-empty interior, then `K` lies on one side of it:
  `K ⊆ {ε π_v ≥ 0}`.  Paper Proposition 8.9(b), case (β).
* `Nivat.cone_trichotomy` — a closed convex cone spanning the plane is the whole plane, a closed
  half-plane, or a closed sector of opening `< π`.  Paper Proposition 8.9(c).
* `Nivat.line_inter_interior_of_univ`, `Nivat.line_inter_interior_of_halfPlane` — a line through
  the origin meets the interior of the plane, and of any half-plane whose boundary it is not
  parallel to.  Used to rule out the first two branches of the trichotomy.
* `Nivat.isClosed_setOf_forall_add_mem` — the translation stabiliser of a closed set is closed.
  This is what supplies `cone_trichotomy`'s `IsClosed` hypothesis for a recession cone.
* `Nivat.forall_add_mem_iff_exists_ray_mem` — the ray criterion for recession directions of a
  closed convex set, and its quantitative consequences
  `Nivat.exists_nat_forall_le_not_mem` and `Nivat.exists_nat_forall_abs_le_not_mem`: along a
  direction that is not a recession direction, the set is left for good, and if neither `±w` is
  a recession direction the set meets every line `x + ℝ w` in a bounded segment.  Used for the
  transverse boundedness of a region in §8.3.  Mathlib has no recession-cone theory.
* `Nivat.exists_long_window` — the slices of a convex set transverse to a two-dimensional
  recession cone grow without bound: every prescribed length is realised on all sufficiently
  high level lines.  This is the growth statement §8.3 needs to find a translate landing in the
  region.
* `Nivat.exists_common_window` — the same, for a finite family of offsets at once: one window,
  valid for every offset simultaneously.  Shifting the base point moves the window by a constant
  while the window grows linearly, so a common sub-window survives.
* `Nivat.exists_forall_ge_piE_exists_zsmul_add_mem` — the lattice form for a region: past a
  threshold on `ε π_v`, every lattice point can be moved into `R` *along `v`*, by an integer
  multiple of `k • v`, simultaneously for a finite family of offsets.  Paper Proposition 8.9(b),
  case (β).  Its docstring records why the seemingly natural strengthening "the region contains
  a half-plane of lattice points" is false.

## Status

Complete; no `sorry`.

The separation lemma carries an explicit `(interior K).Nonempty` hypothesis, which is not
optional: see the counterexample recorded in its docstring.
-/

namespace Nivat

open scoped Pointwise

/-! ### Elementary facts -/

/-- The line `ℝ v` is convex. -/
theorem convex_lineR (v : ℤ × ℤ) : Convex ℝ (lineR v) := by
  rintro _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ a b _ _ _
  exact ⟨a * c₁ + b * c₂, by rw [add_smul, mul_smul, mul_smul]⟩

/-- The set of translations stabilising a closed set is closed: it is the intersection, over the
points `x` of the set, of the preimages of the set under `w ↦ x + w`.

This supplies the `IsClosed` hypothesis of `cone_trichotomy` for the recession cone of a region:
since `recCone R = {w | ∀ x ∈ convHullOf R, x + w ∈ convHullOf R}` and `convHullOf R` is a
`closure`, `isClosed_setOf_forall_add_mem isClosed_closure` has type `IsClosed (recCone R)`. -/
theorem isClosed_setOf_forall_add_mem {C : Set (ℝ × ℝ)} (hC : IsClosed C) :
    IsClosed {w : ℝ × ℝ | ∀ x ∈ C, x + w ∈ C} := by
  have h : {w : ℝ × ℝ | ∀ x ∈ C, x + w ∈ C} = ⋂ x ∈ C, (fun w => x + w) ⁻¹' C := by
    ext w
    constructor
    · intro hw
      exact Set.mem_iInter₂.mpr fun x hx => hw x hx
    · intro hw x hx
      exact Set.mem_iInter₂.mp hw x hx
  rw [h]
  exact isClosed_biInter fun x _ => hC.preimage (continuous_const.add continuous_id)

-- Compatibility check for the intended use (adds no name to the API): the one-liner above really
-- does produce `IsClosed (recCone R)`, so a change to `recCone`'s definition breaks here first.
example (R : Set (ℤ × ℤ)) : IsClosed (recCone R) := isClosed_setOf_forall_add_mem isClosed_closure

/-- A continuous linear functional on `ℝ²` is `y ↦ f (1, 0) y₁ + f (0, 1) y₂`. -/
private lemma strongDual_apply (f : StrongDual ℝ (ℝ × ℝ)) (y : ℝ × ℝ) :
    f y = f (1, 0) * y.1 + f (0, 1) * y.2 := by
  have hy : y = y.1 • ((1 : ℝ), (0 : ℝ)) + y.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  conv_lhs => rw [hy]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- A non-zero linear form `n₁ y₁ + n₂ y₂` vanishing on `v ≠ 0` is a non-zero multiple of
`π_v`; so if it is `≤ 0` on `K`, then `K ⊆ {ε π_v ≥ 0}` for one of the two signs `ε`. -/
private lemma exists_bool_of_forall_nonpos {v : ℤ × ℤ} (hv : v ≠ 0) {n₁ n₂ : ℝ}
    (hperp : n₁ * v.1 + n₂ * v.2 = 0) (hne : ¬ (n₁ = 0 ∧ n₂ = 0)) {K : Set (ℝ × ℝ)}
    (hK : ∀ y ∈ K, n₁ * y.1 + n₂ * y.2 ≤ 0) : ∃ ε : Bool, ∀ y ∈ K, 0 ≤ piER ε v y := by
  have hv' : (v.1 : ℝ) ≠ 0 ∨ (v.2 : ℝ) ≠ 0 := by
    by_contra h
    rw [not_or, not_not, not_not] at h
    exact hv (Prod.ext (by exact_mod_cast h.1) (by exact_mod_cast h.2))
  obtain ⟨lam, hn₁, hn₂⟩ : ∃ lam : ℝ, n₁ = -lam * v.2 ∧ n₂ = lam * v.1 := by
    rcases hv' with h₁ | h₂
    · refine ⟨n₂ / v.1, ?_, (div_mul_cancel₀ n₂ h₁).symm⟩
      rw [neg_mul, div_mul_eq_mul_div, ← neg_div, eq_div_iff h₁]
      linear_combination hperp
    · refine ⟨-n₁ / v.2, ?_, ?_⟩
      · rw [neg_div, neg_neg, div_mul_cancel₀ n₁ h₂]
      · rw [div_mul_eq_mul_div, eq_div_iff h₂]
        linear_combination hperp
  have hform : ∀ y : ℝ × ℝ, n₁ * y.1 + n₂ * y.2 = lam * piR v y := by
    intro y
    rw [hn₁, hn₂, piR]
    ring
  have hlam : lam ≠ 0 := by
    rintro rfl
    exact hne ⟨by rw [hn₁]; ring, by rw [hn₂]; ring⟩
  rcases lt_or_gt_of_ne hlam with hneg | hpos
  · refine ⟨true, fun y hy => ?_⟩
    have h := hK y hy
    rw [hform] at h
    simp only [piER, if_true]
    by_contra hcon
    rw [not_le] at hcon
    exact absurd h (not_le.mpr (mul_pos_of_neg_of_neg hneg hcon))
  · refine ⟨false, fun y hy => ?_⟩
    have h := hK y hy
    rw [hform] at h
    simp only [piER, Bool.false_eq_true, if_false, neg_nonneg]
    by_contra hcon
    rw [not_le] at hcon
    exact absurd h (not_le.mpr (mul_pos hpos hcon))

/-! ### Separation of a line from a cone -/

/-- **Separation of a line from a cone.**  If the line `ℝ v` does not meet the interior of a
convex cone `K` with non-empty interior, then `K` lies on one side of the line:
`K ⊆ {ε π_v ≥ 0}` for some sign `ε`.  Paper Proposition 8.9(b), case (β).

Proof: geometric Hahn–Banach separates the open convex set `interior K` from the convex set
`ℝ v` by a functional `f` with `f < u` on `interior K` and `u ≤ f` on the line; since the line
is a subspace, `f` vanishes on it and `u ≤ 0`, so `f < 0` on `interior K` and hence `f ≤ 0` on
`K ⊆ closure (interior K)`.  A functional vanishing on `v` is a multiple of `π_v`.

`hint` is essential and must not be dropped: without it the statement is false.  Take
`K := {y | y.1 = 0}` (the vertical line, a convex cone) and `v := (1, 0)`.  Then `interior K = ∅`,
so `hdisj` holds vacuously, but `piR v y = y.2` takes both signs on `K`, so neither `ε` works. -/
theorem exists_side_of_line_not_mem_interior_of_nonempty_interior {K : Set (ℝ × ℝ)}
    (hconv : Convex ℝ K) (hcone : ∀ c : ℝ, 0 ≤ c → ∀ y ∈ K, c • y ∈ K) {v : ℤ × ℤ}
    (hv : v ≠ 0) (hint : (interior K).Nonempty)
    (hdisj : ¬ (lineR v ∩ interior K).Nonempty) :
    ∃ ε : Bool, ∀ y ∈ K, 0 ≤ piER ε v y := by
  have _ := hcone
  have hdisj' : Disjoint (interior K) (lineR v) := by
    rw [Set.disjoint_iff_inter_eq_empty, Set.inter_comm]
    exact Set.not_nonempty_iff_eq_empty.mp hdisj
  obtain ⟨f, u, hfK, hfL⟩ :=
    geometric_hahn_banach_open hconv.interior isOpen_interior (convex_lineR v) hdisj'
  -- `f` vanishes on the line and `u ≤ 0`.
  have hfv : f (toReal v) = 0 := by
    by_contra hne
    have h₁ := hfL (((u - 1) / f (toReal v)) • toReal v) ⟨_, rfl⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at h₁
    linarith
  have hu : u ≤ 0 := by
    have h₀ := hfL 0 ⟨0, by simp⟩
    rwa [map_zero] at h₀
  -- `f ≤ 0` on `K`.
  have hfK' : ∀ y ∈ K, f y ≤ 0 := by
    intro y hy
    have hy' : y ∈ closure (interior K) := by
      rw [hconv.closure_interior_eq_closure_of_nonempty_interior hint]
      exact subset_closure hy
    have hcl : closure (interior K) ⊆ {y | f y ≤ 0} :=
      closure_minimal (fun a ha => ((hfK a ha).trans_le hu).le)
        (isClosed_le f.continuous continuous_const)
    exact hcl hy'
  -- Express `f` in coordinates and conclude.
  have hperp : f (1, 0) * v.1 + f (0, 1) * v.2 = 0 := by
    have h := strongDual_apply f (toReal v)
    rw [hfv] at h
    exact h.symm
  have hne : ¬ (f (1, 0) = 0 ∧ f (0, 1) = 0) := by
    rintro ⟨h₁, h₂⟩
    obtain ⟨a, ha⟩ := hint
    have := hfK a ha
    rw [strongDual_apply, h₁, h₂] at this
    linarith
  refine exists_bool_of_forall_nonpos hv hperp hne fun y hy => ?_
  rw [← strongDual_apply]
  exact hfK' y hy

/-! ### Lines through the interior of the plane and of a half-plane -/

/-- A line through the origin meets the interior of the plane. -/
theorem line_inter_interior_of_univ {v : ℤ × ℤ} (hv : v ≠ 0) :
    (lineR v ∩ interior (Set.univ : Set (ℝ × ℝ))).Nonempty := by
  have _ := hv
  exact ⟨0, ⟨0, by simp⟩, by simp⟩

/-- A line through the origin not parallel to the boundary of a closed half-plane meets the
interior of the half-plane: `interior {⟨n, ·⟩ ≥ 0} ⊇ {⟨n, ·⟩ > 0}`, and `c • v` lies there for
`c = ⟨n, v⟩`. -/
theorem line_inter_interior_of_halfPlane {n : ℝ × ℝ} (hn : n ≠ 0) {v : ℤ × ℤ} (hv : v ≠ 0)
    (hnb : n.1 * (v.1 : ℝ) + n.2 * (v.2 : ℝ) ≠ 0) :
    (lineR v ∩ interior {y : ℝ × ℝ | 0 ≤ n.1 * y.1 + n.2 * y.2}).Nonempty := by
  have _ := hn
  have _ := hv
  set c : ℝ := n.1 * (v.1 : ℝ) + n.2 * (v.2 : ℝ) with hcdef
  have hopen : IsOpen {y : ℝ × ℝ | 0 < n.1 * y.1 + n.2 * y.2} :=
    isOpen_lt continuous_const
      ((continuous_const.mul continuous_fst).add (continuous_const.mul continuous_snd))
  have hsub : {y : ℝ × ℝ | 0 < n.1 * y.1 + n.2 * y.2} ⊆ {y | 0 ≤ n.1 * y.1 + n.2 * y.2} :=
    fun y hy => show 0 ≤ n.1 * y.1 + n.2 * y.2 from le_of_lt hy
  refine ⟨c • toReal v, ⟨c, rfl⟩, interior_maximal hsub hopen ?_⟩
  show 0 < n.1 * (c • toReal v).1 + n.2 * (c • toReal v).2
  have hval : n.1 * (c • toReal v).1 + n.2 * (c • toReal v).2 = c * c := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, toReal, hcdef]
    ring
  rw [hval]
  exact mul_self_pos.mpr hnb

/-! ### Classification of planar closed convex cones -/

/-- A convex cone is closed under addition. -/
private lemma add_mem_of_cone {K : Set (ℝ × ℝ)} (hconv : Convex ℝ K)
    (hcone : ∀ c : ℝ, 0 ≤ c → ∀ y ∈ K, c • y ∈ K) {x y : ℝ × ℝ} (hx : x ∈ K) (hy : y ∈ K) :
    x + y ∈ K := by
  have h := hcone 2 (by norm_num) _
    (hconv hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  rwa [smul_add, smul_smul, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul,
    one_smul] at h

/-- The sector spanned by two elements of a convex cone lies in the cone. -/
private lemma sector_subset {K : Set (ℝ × ℝ)} (hconv : Convex ℝ K)
    (hcone : ∀ c : ℝ, 0 ≤ c → ∀ y ∈ K, c • y ∈ K) {w₁ w₂ : ℝ × ℝ} (h₁ : w₁ ∈ K) (h₂ : w₂ ∈ K) :
    {y | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ y = s • w₁ + t • w₂} ⊆ K := by
  rintro _ ⟨s, t, hs, ht, rfl⟩
  exact add_mem_of_cone hconv hcone (hcone s hs _ h₁) (hcone t ht _ h₂)

/-- A sector is closed under non-negative scaling. -/
private lemma sector_smul_mem {w₁ w₂ y : ℝ × ℝ}
    (hy : y ∈ {y | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ y = s • w₁ + t • w₂}) {c : ℝ} (hc : 0 ≤ c) :
    c • y ∈ {y | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ y = s • w₁ + t • w₂} := by
  obtain ⟨s, t, hs, ht, rfl⟩ := hy
  exact ⟨c * s, c * t, mul_nonneg hc hs, mul_nonneg hc ht, by rw [smul_add, smul_smul, smul_smul]⟩

/-- A closed convex cone containing `0` and missing a point `p` lies in a closed half-plane
`{⟨n, ·⟩ ≥ 0}` with `n ≠ 0`: separate `p` from `K` and use that `K` is a cone. -/
private lemma exists_halfPlane_superset {K : Set (ℝ × ℝ)} (hconv : Convex ℝ K)
    (hclosed : IsClosed K) (hcone : ∀ c : ℝ, 0 ≤ c → ∀ y ∈ K, c • y ∈ K)
    (h0 : (0 : ℝ × ℝ) ∈ K) {p : ℝ × ℝ} (hp : p ∉ K) :
    ∃ n : ℝ × ℝ, n ≠ 0 ∧ ∀ y ∈ K, 0 ≤ n.1 * y.1 + n.2 * y.2 := by
  obtain ⟨f, u, hfK, hfp⟩ := geometric_hahn_banach_closed_point hconv hclosed hp
  have hu : 0 < u := by
    have h := hfK 0 h0
    rwa [map_zero] at h
  have hfle : ∀ y ∈ K, f y ≤ 0 := by
    intro y hy
    by_contra hcon
    rw [not_le] at hcon
    have hc : 0 ≤ u / f y + 1 := by
      have := div_pos hu hcon
      linarith
    have h := hfK ((u / f y + 1) • y) (hcone _ hc y hy)
    rw [map_smul, smul_eq_mul, add_mul, one_mul, div_mul_cancel₀ _ hcon.ne'] at h
    linarith
  refine ⟨(-f (1, 0), -f (0, 1)), ?_, fun y hy => ?_⟩
  · intro h
    rw [Prod.mk_eq_zero, neg_eq_zero, neg_eq_zero] at h
    have h' := hfp
    rw [strongDual_apply, h.1, h.2] at h'
    linarith
  · have h := hfle y hy
    rw [strongDual_apply] at h
    show 0 ≤ -f (1, 0) * y.1 + -f (0, 1) * y.2
    linarith

/-- The rotated normal `n^⊥ = (-n₂, n₁)`. -/
private def perp (n : ℝ × ℝ) : ℝ × ℝ := (-n.2, n.1)

private lemma perp_fst (n : ℝ × ℝ) : (perp n).1 = -n.2 := rfl

private lemma perp_snd (n : ℝ × ℝ) : (perp n).2 = n.1 := rfl

/-- Coordinates with respect to the orthogonal basis `(n, n^⊥)`. -/
private lemma decomp {n : ℝ × ℝ} (hn : n.1 * n.1 + n.2 * n.2 ≠ 0) (y : ℝ × ℝ) :
    y = ((n.1 * y.1 + n.2 * y.2) / (n.1 * n.1 + n.2 * n.2)) • n
      + ((-n.2 * y.1 + n.1 * y.2) / (n.1 * n.1 + n.2 * n.2)) • perp n := by
  refine Prod.ext ?_ ?_ <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, perp_fst,
      perp_snd] <;>
    rw [eq_comm, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hn] <;>
    ring

/-- A point with `⟨n, y⟩ > 0` rescales to a point `n + t n^⊥` of the reference line. -/
private lemma smul_eq_add_slope {n y : ℝ × ℝ} (hpos : 0 < n.1 * y.1 + n.2 * y.2) :
    ((n.1 * n.1 + n.2 * n.2) / (n.1 * y.1 + n.2 * y.2)) • y
      = n + ((-n.2 * y.1 + n.1 * y.2) / (n.1 * y.1 + n.2 * y.2)) • perp n := by
  have hne := hpos.ne'
  refine Prod.ext ?_ ?_ <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, perp_fst,
      perp_snd] <;>
    field_simp <;> ring

/-- `(a / b) * (b / a) = 1`. -/
private lemma div_mul_div_self_eq_one {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    a / b * (b / a) = 1 := by
  rw [div_mul_div_comm, mul_comm a b, div_self (mul_ne_zero hb ha)]

/-- If the slopes `{t | n + t w ∈ K}` of a closed cone are unbounded above, the limiting
direction `w` lies in `K`. -/
private lemma mem_of_not_bddAbove {K : Set (ℝ × ℝ)} (hclosed : IsClosed K)
    (hcone : ∀ c : ℝ, 0 ≤ c → ∀ y ∈ K, c • y ∈ K) {n w : ℝ × ℝ}
    (hJ : ¬ BddAbove {t : ℝ | n + t • w ∈ K}) : w ∈ K := by
  rw [← hclosed.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨t, ht, htgt⟩ := not_bddAbove_iff.mp hJ (max 0 (‖n‖ / ε))
  have ht0 : 0 < t := (le_max_left _ _).trans_lt htgt
  have htn : ‖n‖ / ε < t := (le_max_right _ _).trans_lt htgt
  refine ⟨t⁻¹ • (n + t • w), hcone _ (inv_nonneg.mpr ht0.le) _ ht, ?_⟩
  rw [dist_eq_norm, smul_add, smul_smul, inv_mul_cancel₀ ht0.ne', one_smul,
    show w - (t⁻¹ • n + w) = -(t⁻¹ • n) by abel, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr ht0), inv_mul_lt_iff₀ ht0]
  exact (div_lt_iff₀ hε).mp htn

/-- If the slopes `{t | n + t w ∈ K}` of a closed cone are unbounded below, `-w ∈ K`. -/
private lemma neg_mem_of_not_bddBelow {K : Set (ℝ × ℝ)} (hclosed : IsClosed K)
    (hcone : ∀ c : ℝ, 0 ≤ c → ∀ y ∈ K, c • y ∈ K) {n w : ℝ × ℝ}
    (hJ : ¬ BddBelow {t : ℝ | n + t • w ∈ K}) : -w ∈ K := by
  refine mem_of_not_bddAbove hclosed hcone (n := n) ?_
  intro hbdd
  apply hJ
  rw [← bddAbove_neg]
  have hset : -{t : ℝ | n + t • w ∈ K} = {t : ℝ | n + t • -w ∈ K} := by
    ext t
    rw [Set.mem_neg]
    show n + (-t) • w ∈ K ↔ n + t • -w ∈ K
    rw [neg_smul, smul_neg]
  rw [hset]
  exact hbdd

/-- **Trichotomy for planar closed convex cones.**  A closed convex cone `K ⊆ ℝ²` that spans
the plane is the whole plane, a closed half-plane `{⟨n, ·⟩ ≥ 0}`, or a closed sector
`{s w₁ + t w₂ : s, t ≥ 0}` with `w₁, w₂` linearly independent (opening strictly between `0`
and `π`).  Paper Proposition 8.9(c).

Proof.  If `K ≠ ℝ²`, separate a missing point to get `K ⊆ {⟨n, ·⟩ ≥ 0}`, `n ≠ 0`.  Every
`y ∈ K` with `⟨n, y⟩ > 0` rescales to a point `n + t n^⊥` of the line `⟨n, ·⟩ = |n|²`; the set
`J` of such slopes `t` is a closed interval (closed, convex, non-empty because `K` spans the
plane), and the points of `K` on the boundary line `⟨n, ·⟩ = 0` are multiples of `n^⊥` that,
by closedness, are present exactly when `J` is unbounded in the corresponding direction.
The four shapes `J = ℝ`, `[a, ∞)`, `(-∞, b]`, `[a, b]` give the half-plane and the three
sector presentations. -/
theorem cone_trichotomy {K : Set (ℝ × ℝ)} (hconv : Convex ℝ K) (hclosed : IsClosed K)
    (hcone : ∀ c : ℝ, 0 ≤ c → ∀ y ∈ K, c • y ∈ K) (hspan : SpansPlane K) :
    K = Set.univ
    ∨ (∃ n : ℝ × ℝ, n ≠ 0 ∧ K = {y | 0 ≤ n.1 * y.1 + n.2 * y.2})
    ∨ (∃ w₁ w₂ : ℝ × ℝ, w₁.1 * w₂.2 - w₁.2 * w₂.1 ≠ 0 ∧
        K = {y | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ y = s • w₁ + t • w₂}) := by
  classical
  obtain ⟨x, hx, y, hy, hdet⟩ := hspan
  have h0 : (0 : ℝ × ℝ) ∈ K := by simpa using hcone 0 le_rfl x hx
  by_cases huniv : K = Set.univ
  · exact Or.inl huniv
  right
  obtain ⟨p, hp⟩ : ∃ p, p ∉ K := by
    by_contra h
    rw [not_exists] at h
    exact huniv (Set.eq_univ_iff_forall.mpr fun p => not_not.mp (h p))
  obtain ⟨n, hn, hKn⟩ := exists_halfPlane_superset hconv hclosed hcone h0 hp
  -- Set-up: the orthogonal basis `(n, m)`, `m = n^⊥`, and the slope set `J`.
  have hn' : n.1 ≠ 0 ∨ n.2 ≠ 0 := by
    by_contra h
    rw [not_or, not_not, not_not] at h
    exact hn (Prod.ext h.1 h.2)
  have hNpos : 0 < n.1 * n.1 + n.2 * n.2 := by
    have h1 := mul_self_nonneg n.1
    have h2 := mul_self_nonneg n.2
    rcases hn' with h | h
    · have := mul_self_pos.mpr h; linarith
    · have := mul_self_pos.mpr h; linarith
  have hN0 : n.1 * n.1 + n.2 * n.2 ≠ 0 := hNpos.ne'
  set m : ℝ × ℝ := perp n with hmdef
  set J : Set ℝ := {t | n + t • m ∈ K} with hJdef
  have hJmem : ∀ {t : ℝ}, t ∈ J ↔ n + t • m ∈ K := fun {t} => Iff.rfl
  have hJclosed : IsClosed J := by
    have h : Continuous fun t : ℝ => n + t • m :=
      continuous_const.add (continuous_id.smul continuous_const)
    exact IsClosed.preimage h hclosed
  have hJconv : Convex ℝ J := by
    intro t₁ ht₁ t₂ ht₂ a b ha hb hab
    have h := hconv (hJmem.mp ht₁) (hJmem.mp ht₂) ha hb hab
    show n + (a * t₁ + b * t₂) • m ∈ K
    have heq : n + (a * t₁ + b * t₂) • m = a • (n + t₁ • m) + b • (n + t₂ • m) := by
      have hn1 : n = (a + b) • n := by rw [hab, one_smul]
      conv_lhs => rw [hn1]
      rw [smul_add, smul_add, smul_smul, smul_smul, add_smul, add_smul]
      abel
    rw [heq]
    exact h
  have hJord : J.OrdConnected := hJconv.ordConnected
  -- Points of `K` off the boundary line have their slope in `J`.
  have hslope : ∀ y ∈ K, 0 < n.1 * y.1 + n.2 * y.2 →
      (-n.2 * y.1 + n.1 * y.2) / (n.1 * y.1 + n.2 * y.2) ∈ J := by
    intro y hy hpos
    rw [hJmem, hmdef, ← smul_eq_add_slope hpos]
    exact hcone _ (div_nonneg hNpos.le hpos.le) y hy
  -- Rescaling a point of `K` off the boundary line back from the reference line.
  have hrescale : ∀ y : ℝ × ℝ, 0 < n.1 * y.1 + n.2 * y.2 →
      ((n.1 * y.1 + n.2 * y.2) / (n.1 * n.1 + n.2 * n.2)) •
        (n + ((-n.2 * y.1 + n.1 * y.2) / (n.1 * y.1 + n.2 * y.2)) • m) = y := by
    intro y hpos
    rw [hmdef, ← smul_eq_add_slope hpos, smul_smul,
      div_mul_div_self_eq_one hpos.ne' hN0, one_smul]
  -- Points of `K` on the boundary line are multiples of `m`, and force `±m ∈ K`.
  have hbdry : ∀ y ∈ K, n.1 * y.1 + n.2 * y.2 = 0 →
      ∃ c : ℝ, y = c • m ∧ (0 < c → m ∈ K) ∧ (c < 0 → -m ∈ K) := by
    intro y hy hα
    obtain ⟨c, hc⟩ : ∃ c : ℝ, y = c • m := by
      refine ⟨(-n.2 * y.1 + n.1 * y.2) / (n.1 * n.1 + n.2 * n.2), ?_⟩
      have h := decomp hN0 y
      rwa [hα, zero_div, zero_smul, zero_add] at h
    refine ⟨c, hc, fun hcpos => ?_, fun hcneg => ?_⟩
    · have h := hcone c⁻¹ (inv_nonneg.mpr hcpos.le) y hy
      rwa [hc, smul_smul, inv_mul_cancel₀ hcpos.ne', one_smul] at h
    · have h := hcone (-c)⁻¹ (inv_nonneg.mpr (by linarith)) y hy
      rwa [hc, smul_smul, inv_neg, neg_mul, inv_mul_cancel₀ hcneg.ne, neg_one_smul] at h
  -- `J` is non-empty: not both spanning vectors lie on the boundary line.
  have hJne : J.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hzero : ∀ z ∈ K, n.1 * z.1 + n.2 * z.2 = 0 := by
      intro z hz
      rcases (hKn z hz).lt_or_eq with hpos | h
      · have := hslope z hz hpos
        rw [hcon] at this
        exact absurd this (Set.notMem_empty _)
      · exact h.symm
    obtain ⟨c₁, hc₁, -, -⟩ := hbdry x hx (hzero x hx)
    obtain ⟨c₂, hc₂, -, -⟩ := hbdry y hy (hzero y hy)
    apply hdet
    rw [hc₁, hc₂]
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, hmdef, perp_fst, perp_snd]
    ring
  -- `m ∈ K` forces `J` unbounded above, and `-m ∈ K` forces `J` unbounded below.
  have hm_unb : m ∈ K → ¬ BddAbove J := by
    intro hm ⟨M, hM⟩
    obtain ⟨t₀, ht₀⟩ := hJne
    have hle : t₀ ≤ M := hM ht₀
    have hmem : t₀ + (M - t₀ + 1) ∈ J := by
      rw [hJmem, add_smul, ← add_assoc]
      exact add_mem_of_cone hconv hcone (hJmem.mp ht₀) (hcone _ (by linarith) m hm)
    have := hM hmem
    linarith
  have hnegm_unb : -m ∈ K → ¬ BddBelow J := by
    intro hm ⟨M, hM⟩
    obtain ⟨t₀, ht₀⟩ := hJne
    have hle : M ≤ t₀ := hM ht₀
    have hmem : t₀ + (-(t₀ - M + 1)) ∈ J := by
      rw [hJmem, add_smul, ← add_assoc, neg_smul, ← smul_neg]
      exact add_mem_of_cone hconv hcone (hJmem.mp ht₀) (hcone _ (by linarith) (-m) hm)
    have := hM hmem
    linarith
  -- Assembling `K ⊆ S` for a candidate sector `S` from the two kinds of points.
  have hassemble : ∀ w₁ w₂ : ℝ × ℝ,
      (∀ t ∈ J, n + t • m ∈ {y | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ y = s • w₁ + t • w₂}) →
      (∀ y ∈ K, n.1 * y.1 + n.2 * y.2 = 0 →
        y ∈ {y | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ y = s • w₁ + t • w₂}) →
      K ⊆ {y | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ y = s • w₁ + t • w₂} := by
    intro w₁ w₂ hJS hbS y hy
    rcases (hKn y hy).lt_or_eq with hpos | hzero
    · have h := sector_smul_mem (hJS _ (hslope y hy hpos))
        (div_nonneg hpos.le hNpos.le : 0 ≤ (n.1 * y.1 + n.2 * y.2) / (n.1 * n.1 + n.2 * n.2))
      rwa [hrescale y hpos] at h
    · exact hbS y hy hzero.symm
  -- The four shapes of `J`.
  by_cases hA : BddAbove J <;> by_cases hB : BddBelow J
  · -- `J = [a, b]`: a sector with two finite boundary rays.
    right
    set a : ℝ := sInf J with hadef
    set b : ℝ := sSup J with hbdef
    have ha : a ∈ J := hJclosed.csInf_mem hJne hB
    have hb : b ∈ J := hJclosed.csSup_mem hJne hA
    have hab : a ≤ b := csInf_le_csSup hJne hB hA
    have hbdry0 : ∀ y ∈ K, n.1 * y.1 + n.2 * y.2 = 0 → y = 0 := by
      intro y hy hα
      obtain ⟨c, hc, hcpos, hcneg⟩ := hbdry y hy hα
      rcases lt_trichotomy c 0 with hlt | heq | hgt
      · exact absurd hB (hnegm_unb (hcneg hlt))
      · rw [hc, heq, zero_smul]
      · exact absurd hA (hm_unb (hcpos hgt))
    have hab' : a ≠ b := by
      intro heq
      -- every point of `K` is a multiple of `n + a • m`, contradicting `SpansPlane`.
      have hray : ∀ z ∈ K, ∃ c : ℝ, z = c • (n + a • m) := by
        intro z hz
        rcases (hKn z hz).lt_or_eq with hpos | hzero
        · have ht := hslope z hz hpos
          have hta : (-n.2 * z.1 + n.1 * z.2) / (n.1 * z.1 + n.2 * z.2) = a :=
            le_antisymm (by rw [heq]; exact le_csSup hA ht) (csInf_le hB ht)
          refine ⟨(n.1 * z.1 + n.2 * z.2) / (n.1 * n.1 + n.2 * n.2), ?_⟩
          rw [← hta, hrescale z hpos]
        · exact ⟨0, by rw [hbdry0 z hz hzero.symm, zero_smul]⟩
      obtain ⟨c₁, hc₁⟩ := hray x hx
      obtain ⟨c₂, hc₂⟩ := hray y hy
      apply hdet
      rw [hc₁, hc₂]
      simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
      ring
    have hba : b - a ≠ 0 := sub_ne_zero.mpr hab'.symm
    refine ⟨n + a • m, n + b • m, ?_, Set.Subset.antisymm ?_ ?_⟩
    · intro h
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, hmdef,
        perp_fst, perp_snd] at h
      apply mul_ne_zero hba hN0
      linear_combination h
    · refine hassemble _ _ (fun t ht => ?_) (fun y hy hα => ?_)
      · have hta : a ≤ t := csInf_le hB ht
        have htb : t ≤ b := le_csSup hA ht
        refine ⟨(b - t) / (b - a), (t - a) / (b - a), div_nonneg (by linarith) (by linarith),
          div_nonneg (by linarith) (by linarith), ?_⟩
        refine Prod.ext ?_ ?_ <;>
          simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
          field_simp <;> ring
      · rw [hbdry0 y hy hα]
        exact ⟨0, 0, le_rfl, le_rfl, by simp⟩
    · exact sector_subset hconv hcone (hJmem.mp ha) (hJmem.mp hb)
  · -- `J = (-∞, b]`: a sector with boundary rays `n + b • m` and `-m`.
    right
    have hm : -m ∈ K := neg_mem_of_not_bddBelow hclosed hcone (n := n) (w := m) hB
    set b : ℝ := sSup J with hbdef
    have hb : b ∈ J := hJclosed.csSup_mem hJne hA
    refine ⟨n + b • m, -m, ?_, Set.Subset.antisymm ?_ ?_⟩
    · intro h
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_neg,
        Prod.snd_neg, smul_eq_mul, hmdef, perp_fst, perp_snd] at h
      apply hN0
      linear_combination -h
    · refine hassemble _ _ (fun t ht => ?_) (fun y hy hα => ?_)
      · have htb : t ≤ b := le_csSup hA ht
        refine ⟨1, b - t, zero_le_one, by linarith, ?_⟩
        rw [one_smul, smul_neg, add_assoc, ← sub_eq_add_neg, ← sub_smul,
          show b - (b - t) = t by ring]
      · obtain ⟨c, hc, hcpos, -⟩ := hbdry y hy hα
        have hc0 : c ≤ 0 := by
          by_contra hcon
          rw [not_le] at hcon
          exact absurd hA (hm_unb (hcpos hcon))
        exact ⟨0, -c, le_rfl, by linarith,
          by rw [hc, zero_smul, zero_add, neg_smul, smul_neg, neg_neg]⟩
    · exact sector_subset hconv hcone (hJmem.mp hb) hm
  · -- `J = [a, ∞)`: a sector with boundary rays `n + a • m` and `m`.
    right
    have hm : m ∈ K := mem_of_not_bddAbove hclosed hcone (n := n) (w := m) hA
    set a : ℝ := sInf J with hadef
    have ha : a ∈ J := hJclosed.csInf_mem hJne hB
    refine ⟨n + a • m, m, ?_, Set.Subset.antisymm ?_ ?_⟩
    · intro h
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, hmdef,
        perp_fst, perp_snd] at h
      apply hN0
      linear_combination h
    · refine hassemble _ _ (fun t ht => ?_) (fun y hy hα => ?_)
      · have hta : a ≤ t := csInf_le hB ht
        refine ⟨1, t - a, zero_le_one, by linarith, ?_⟩
        rw [one_smul, add_assoc, ← add_smul, show a + (t - a) = t by ring]
      · obtain ⟨c, hc, -, hcneg⟩ := hbdry y hy hα
        have hc0 : 0 ≤ c := by
          by_contra hcon
          rw [not_le] at hcon
          exact absurd hB (hnegm_unb (hcneg hcon))
        exact ⟨0, c, le_rfl, hc0, by rw [hc, zero_smul, zero_add]⟩
    · exact sector_subset hconv hcone (hJmem.mp ha) hm
  · -- `J = ℝ`: the closed half-plane `{⟨n, ·⟩ ≥ 0}`.
    left
    have hm : m ∈ K := mem_of_not_bddAbove hclosed hcone (n := n) (w := m) hA
    have hnegm : -m ∈ K := neg_mem_of_not_bddBelow hclosed hcone (n := n) (w := m) hB
    refine ⟨n, hn, Set.Subset.antisymm hKn fun y hy => ?_⟩
    rcases (show 0 ≤ n.1 * y.1 + n.2 * y.2 from hy).lt_or_eq with hpos | hzero
    · -- the slope of `y` lies in `J`, which is all of `ℝ`
      obtain ⟨t₁, ht₁, ht₁lt⟩ :=
        not_bddBelow_iff.mp hB ((-n.2 * y.1 + n.1 * y.2) / (n.1 * y.1 + n.2 * y.2))
      obtain ⟨t₂, ht₂, ht₂gt⟩ :=
        not_bddAbove_iff.mp hA ((-n.2 * y.1 + n.1 * y.2) / (n.1 * y.1 + n.2 * y.2))
      have ht : (-n.2 * y.1 + n.1 * y.2) / (n.1 * y.1 + n.2 * y.2) ∈ J :=
        hJord.out ht₁ ht₂ ⟨ht₁lt.le, ht₂gt.le⟩
      have h := hcone ((n.1 * y.1 + n.2 * y.2) / (n.1 * n.1 + n.2 * n.2))
        (div_nonneg hpos.le hNpos.le) _ (hJmem.mp ht)
      rwa [hrescale y hpos] at h
    · obtain ⟨c, hc⟩ : ∃ c : ℝ, y = c • m := by
        refine ⟨(-n.2 * y.1 + n.1 * y.2) / (n.1 * n.1 + n.2 * n.2), ?_⟩
        have h := decomp hN0 y
        rwa [← hzero, zero_div, zero_smul, zero_add] at h
      rw [hc]
      rcases le_or_gt 0 c with hc0 | hc0
      · exact hcone c hc0 m hm
      · have h := hcone (-c) (by linarith) (-m) hnegm
        rwa [smul_neg, neg_smul, neg_neg] at h

/-! ### Recession directions of a closed convex set -/

/-- Iterating a recession step: if `C + w ⊆ C` then `C + n • w ⊆ C` for every `n : ℕ`. -/
private lemma add_nsmul_mem_of_forall_add_mem {C : Set (ℝ × ℝ)} {w : ℝ × ℝ}
    (hstep : ∀ x ∈ C, x + w ∈ C) (n : ℕ) : ∀ x ∈ C, x + (n : ℝ) • w ∈ C := by
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih =>
    intro x hx
    have h := hstep _ (ih x hx)
    have heq : x + (n : ℝ) • w + w = x + ((n + 1 : ℕ) : ℝ) • w := by
      push_cast
      rw [add_smul, one_smul, add_assoc]
    rwa [heq] at h

/-- On a convex set, `x ∈ C` and `x + s • w ∈ C` give `x + t • w ∈ C` for every `0 ≤ t ≤ s`. -/
private lemma add_smul_mem_of_le {C : Set (ℝ × ℝ)} (hconv : Convex ℝ C) {x w : ℝ × ℝ}
    (hx : x ∈ C) {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t) (hts : t ≤ s) (hxs : x + s • w ∈ C) :
    x + t • w ∈ C := by
  have hlam0 : 0 ≤ t / s := div_nonneg ht hs.le
  have hlam1 : t / s ≤ 1 := (div_le_one hs).mpr hts
  have h := hconv hx hxs (by linarith : (0 : ℝ) ≤ 1 - t / s) hlam0 (by ring)
  have heq : (1 - t / s) • x + (t / s) • (x + s • w) = x + t • w := by
    rw [smul_add, smul_smul, div_mul_cancel₀ _ hs.ne', sub_smul, one_smul]
    abel
  rwa [heq] at h

/-- A recession direction of a convex set generates a whole ray from each of its points: this
is the elementary half of `forall_add_mem_iff_exists_ray_mem`, needing only convexity. -/
theorem ray_mem_of_forall_add_mem {C : Set (ℝ × ℝ)} (hconv : Convex ℝ C) {w : ℝ × ℝ}
    (hstep : ∀ x ∈ C, x + w ∈ C) {x : ℝ × ℝ} (hx : x ∈ C) {t : ℝ} (ht : 0 ≤ t) :
    x + t • w ∈ C := by
  rcases ht.lt_or_eq with htpos | ht0
  · obtain ⟨n, hn⟩ := exists_nat_ge t
    exact add_smul_mem_of_le hconv hx (htpos.trans_le hn) ht hn
      (add_nsmul_mem_of_forall_add_mem hstep n x hx)
  · rw [← ht0, zero_smul, add_zero]
    exact hx

/-- **Closedness upgrades one recession ray to all of them.**  If `C` is closed and convex and
the ray from a single `x₀ ∈ C` in direction `w` stays in `C`, then so does the ray from every
point of `C`.

This is the only step of the recession-cone characterisation with real content, and it is where
closedness is used: for the convex but non-closed `C = {y | 0 < y.2} ∪ {0}` and `w = (1, 0)` the
ray from `(0, 1)` stays in `C` while the ray from `0` leaves it immediately.

Proof: for `y ∈ C` and `t ≥ 0`, the point `(1 - t/s) • y + (t/s) • (x₀ + s • w)` lies in `C` for
every `s ≥ t` and equals `y + t • w + (t/s) • (x₀ - y)`, which tends to `y + t • w` as
`s → ∞`. -/
theorem forall_ray_mem_of_ray_mem {C : Set (ℝ × ℝ)} (hconv : Convex ℝ C) (hclosed : IsClosed C)
    {w x₀ : ℝ × ℝ} (hray : ∀ s : ℝ, 0 ≤ s → x₀ + s • w ∈ C) {y : ℝ × ℝ}
    (hy : y ∈ C) {t : ℝ} (ht : 0 ≤ t) : y + t • w ∈ C := by
  rcases ht.lt_or_eq with htpos | ht0
  · rw [← hclosed.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨s, hs⟩ := exists_gt (max t (t * ‖y - x₀‖ / ε))
    have hst : t < s := (le_max_left _ _).trans_lt hs
    have hsb : t * ‖y - x₀‖ / ε < s := (le_max_right _ _).trans_lt hs
    have hspos : (0 : ℝ) < s := htpos.trans hst
    have hlam0 : 0 ≤ t / s := div_nonneg ht hspos.le
    have hlam1 : t / s ≤ 1 := (div_le_one hspos).mpr hst.le
    refine ⟨(1 - t / s) • y + (t / s) • (x₀ + s • w),
      hconv hy (hray s hspos.le) (by linarith) hlam0 (by ring), ?_⟩
    have heq : y + t • w - ((1 - t / s) • y + (t / s) • (x₀ + s • w)) = (t / s) • (y - x₀) := by
      rw [smul_add, smul_smul, div_mul_cancel₀ _ hspos.ne', sub_smul, one_smul, smul_sub]
      abel
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam0,
      div_mul_eq_mul_div, div_lt_iff₀ hspos]
    have hmul : t * ‖y - x₀‖ < s * ε := (div_lt_iff₀ hε).mp hsb
    have hcomm : s * ε = ε * s := mul_comm s ε
    linarith
  · rw [← ht0, zero_smul, add_zero]
    exact hy

/-- **Ray criterion for recession directions.**  For a non-empty closed convex `C ⊆ ℝ²`, the
translation `x ↦ x + w` maps `C` into itself iff the ray from *some* point of `C` in direction
`w` stays in `C`.

Mathlib has no recession-cone theory, so this is proved from scratch.  With `C := convHullOf R`
the left-hand side is by definition `w ∈ recCone R`, so no rewriting is needed downstream. -/
theorem forall_add_mem_iff_exists_ray_mem {C : Set (ℝ × ℝ)} (hconv : Convex ℝ C)
    (hclosed : IsClosed C) (hne : C.Nonempty) (w : ℝ × ℝ) :
    (∀ x ∈ C, x + w ∈ C) ↔ ∃ x ∈ C, ∀ t : ℝ, 0 ≤ t → x + t • w ∈ C := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, hx, fun t ht => ray_mem_of_forall_add_mem hconv h hx ht⟩
  · rintro ⟨x₀, hx₀, hray⟩ y hy
    have _ := hx₀
    have h := forall_ray_mem_of_ray_mem hconv hclosed hray hy zero_le_one
    rwa [one_smul] at h

/-- Once a ray issued from a point of a convex set has left the set, it stays out. -/
theorem not_mem_of_le_of_not_mem {C : Set (ℝ × ℝ)} (hconv : Convex ℝ C) {x w : ℝ × ℝ}
    (hx : x ∈ C) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (h₀ : x + t₀ • w ∉ C) {t : ℝ} (ht : t₀ ≤ t) :
    x + t • w ∉ C := by
  intro hmem
  rcases ht₀.lt_or_eq with ht₀pos | ht₀zero
  · exact h₀ (add_smul_mem_of_le hconv hx (ht₀pos.trans_le ht) ht₀ ht hmem)
  · exact h₀ (by rw [← ht₀zero, zero_smul, add_zero]; exact hx)

/-- **Escape along a non-recession direction.**  If `x ↦ x + w` does not map the closed convex
set `C` into itself, then the ray in direction `w` from any point of `C` leaves `C` for good:
there is `N : ℕ` with `x + t • w ∉ C` for every `t ≥ N`. -/
theorem exists_nat_forall_le_not_mem {C : Set (ℝ × ℝ)} (hconv : Convex ℝ C) (hclosed : IsClosed C)
    {w : ℝ × ℝ} (hw : ¬ ∀ x ∈ C, x + w ∈ C) {x : ℝ × ℝ} (hx : x ∈ C) :
    ∃ N : ℕ, ∀ t : ℝ, (N : ℝ) ≤ t → x + t • w ∉ C := by
  obtain ⟨t₀, ht₀, h₀⟩ : ∃ t₀ : ℝ, 0 ≤ t₀ ∧ x + t₀ • w ∉ C := by
    by_contra hcon
    refine hw ((forall_add_mem_iff_exists_ray_mem hconv hclosed ⟨x, hx⟩ w).mpr
      ⟨x, hx, fun t ht => ?_⟩)
    by_contra hmem
    exact hcon ⟨t, ht, hmem⟩
  obtain ⟨N, hN⟩ := exists_nat_ge t₀
  exact ⟨N, fun t ht => not_mem_of_le_of_not_mem hconv hx ht₀ h₀ (hN.trans ht)⟩

/-- **Boundedness along a non-recession line.**  If neither `w` nor `-w` is a recession
direction of the closed convex set `C`, then `C` meets every line `x + ℝ w` in a bounded
segment: there is `N : ℕ` with `x + t • w ∉ C` whenever `N ≤ |t|`.

No hypothesis is placed on `x`; if the line misses `C` entirely, `N = 0` works. -/
theorem exists_nat_forall_abs_le_not_mem {C : Set (ℝ × ℝ)} (hconv : Convex ℝ C)
    (hclosed : IsClosed C) {w : ℝ × ℝ} (hw : ¬ ∀ x ∈ C, x + w ∈ C)
    (hw' : ¬ ∀ x ∈ C, x + -w ∈ C) (x : ℝ × ℝ) :
    ∃ N : ℕ, ∀ t : ℝ, (N : ℝ) ≤ |t| → x + t • w ∉ C := by
  by_cases hmeet : ∃ t₀ : ℝ, x + t₀ • w ∈ C
  · obtain ⟨t₀, ht₀⟩ := hmeet
    obtain ⟨N₁, hN₁⟩ := exists_nat_forall_le_not_mem hconv hclosed hw ht₀
    obtain ⟨N₂, hN₂⟩ := exists_nat_forall_le_not_mem hconv hclosed hw' ht₀
    obtain ⟨N₀, hN₀⟩ := exists_nat_ge |t₀|
    refine ⟨N₁ + N₂ + N₀, fun t ht hmem => ?_⟩
    have hcast : (N₁ : ℝ) + (N₂ : ℝ) + (N₀ : ℝ) ≤ |t| := by push_cast at ht; linarith
    have h1 : (0 : ℝ) ≤ (N₁ : ℝ) := Nat.cast_nonneg N₁
    have h2 : (0 : ℝ) ≤ (N₂ : ℝ) := Nat.cast_nonneg N₂
    rcases le_or_gt 0 t with htsign | htsign
    · have habs : |t| = t := abs_of_nonneg htsign
      have hge : (N₁ : ℝ) ≤ t - t₀ := by
        have := le_abs_self t₀
        rw [habs] at hcast
        linarith
      have heq : x + t₀ • w + (t - t₀) • w = x + t • w := by
        rw [add_assoc, ← add_smul, show t₀ + (t - t₀) = t by ring]
      exact hN₁ (t - t₀) hge (by rw [heq]; exact hmem)
    · have habs : |t| = -t := abs_of_neg htsign
      have hge : (N₂ : ℝ) ≤ t₀ - t := by
        have := neg_abs_le t₀
        rw [habs] at hcast
        linarith
      have heq : x + t₀ • w + (t₀ - t) • (-w) = x + t • w := by
        rw [smul_neg, ← neg_smul, add_assoc, ← add_smul, show t₀ + -(t₀ - t) = t by ring]
      exact hN₂ (t₀ - t) hge (by rw [heq]; exact hmem)
  · exact ⟨0, fun t _ hmem => hmeet ⟨t, hmem⟩⟩

/-! ### Growth of the slices transverse to a two-dimensional recession cone -/

/-- Two vectors orthogonal to the same non-zero `n` are parallel. -/
private lemma exists_smul_of_orthogonal {n w z : ℝ × ℝ} (hn : n ≠ 0) (hw0 : w ≠ 0)
    (hw : n.1 * w.1 + n.2 * w.2 = 0) (hz : n.1 * z.1 + n.2 * z.2 = 0) :
    ∃ r : ℝ, z = r • w := by
  have hn' : n.1 ≠ 0 ∨ n.2 ≠ 0 := by
    by_contra h
    rw [not_or, not_not, not_not] at h
    exact hn (Prod.ext h.1 h.2)
  have hdet : w.1 * z.2 - w.2 * z.1 = 0 := by
    have k1 : n.1 * (w.1 * z.2 - w.2 * z.1) = 0 := by linear_combination z.2 * hw - w.2 * hz
    have k2 : n.2 * (w.1 * z.2 - w.2 * z.1) = 0 := by linear_combination w.1 * hz - z.1 * hw
    rcases hn' with h | h
    · exact (mul_eq_zero.mp k1).resolve_left h
    · exact (mul_eq_zero.mp k2).resolve_left h
  have hw' : w.1 ≠ 0 ∨ w.2 ≠ 0 := by
    by_contra h
    rw [not_or, not_not, not_not] at h
    exact hw0 (Prod.ext h.1 h.2)
  rcases hw' with h | h
  · refine ⟨z.1 / w.1, Prod.ext ?_ ?_⟩
    · simp only [Prod.smul_fst, smul_eq_mul]
      rw [div_mul_cancel₀ _ h]
    · simp only [Prod.smul_snd, smul_eq_mul]
      rw [div_mul_eq_mul_div, eq_div_iff h]
      linear_combination hdet
  · refine ⟨z.2 / w.2, Prod.ext ?_ ?_⟩
    · simp only [Prod.smul_fst, smul_eq_mul]
      rw [div_mul_eq_mul_div, eq_div_iff h]
      linear_combination -hdet
    · simp only [Prod.smul_snd, smul_eq_mul]
      rw [div_mul_cancel₀ _ h]

/-- Two points on the same level line of `n` differ by a multiple of a direction `w` spanning
`ker n`. -/
private lemma exists_smul_sub_of_level {n w : ℝ × ℝ} (hn : n ≠ 0) (hw0 : w ≠ 0)
    (hw : n.1 * w.1 + n.2 * w.2 = 0) {p y : ℝ × ℝ}
    (hlev : n.1 * p.1 + n.2 * p.2 = n.1 * y.1 + n.2 * y.2) : ∃ r : ℝ, p = y + r • w := by
  obtain ⟨r, hr⟩ := exists_smul_of_orthogonal hn hw0 hw (z := p - y)
    (by simp only [Prod.fst_sub, Prod.snd_sub]; linear_combination hlev)
  exact ⟨r, by rw [← hr]; abel⟩

/-- Non-negative combinations of two recession directions may be added to any point of a convex
set without leaving it. -/
theorem add_recession_pair_mem {C : Set (ℝ × ℝ)} (hconv : Convex ℝ C) {u₁ u₂ : ℝ × ℝ}
    (hu₁ : ∀ x ∈ C, x + u₁ ∈ C) (hu₂ : ∀ x ∈ C, x + u₂ ∈ C) {x : ℝ × ℝ} (hx : x ∈ C)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) : x + s • u₁ + t • u₂ ∈ C :=
  ray_mem_of_forall_add_mem hconv hu₂ (ray_mem_of_forall_add_mem hconv hu₁ hx hs) ht

/-- **The slices of `C` transverse to a two-dimensional recession cone grow without bound.**

Let `u₁, u₂` be recession directions of the convex set `C`, linearly independent and both on the
positive side of the linear form `y ↦ ⟨n, y⟩`, and let `w ≠ 0` span `ker ⟨n, ·⟩`, so that the
level sets of `⟨n, ·⟩` are exactly the lines `y + ℝ w`.  Then for any prescribed length `L`, all
sufficiently high level lines meet `C` in a segment of length at least `L` measured in units of
`w`: there is a threshold `T` such that every `y` with `⟨n, y⟩ ≥ T` admits `r₀` with
`y + r • w ∈ C` for all `r ∈ [r₀, r₀ + L]`.

Note that `y` is arbitrary on its level line — it need not lie in `C` — because `y + ℝ w` *is*
that level line.  Closedness is not needed.

Proof: at level `⟨n, y⟩ = ⟨n, x₀⟩ + d` the sector `x₀ + ℝ₊u₁ + ℝ₊u₂ ⊆ C` has the two endpoints
`x₀ + (d/α) • u₁` and `x₀ + (d/β) • u₂`, where `α = ⟨n, u₁⟩` and `β = ⟨n, u₂⟩`.  Their difference
is `(d/(αβ)) • (β • u₁ - α • u₂)`, a non-zero multiple of `w` growing linearly in `d`. -/
theorem exists_long_window {C : Set (ℝ × ℝ)} (hconv : Convex ℝ C) {x₀ u₁ u₂ w n : ℝ × ℝ}
    (hx₀ : x₀ ∈ C) (hu₁ : ∀ x ∈ C, x + u₁ ∈ C) (hu₂ : ∀ x ∈ C, x + u₂ ∈ C) (hw0 : w ≠ 0)
    (hw : n.1 * w.1 + n.2 * w.2 = 0) (h₁ : 0 < n.1 * u₁.1 + n.2 * u₁.2)
    (h₂ : 0 < n.1 * u₂.1 + n.2 * u₂.2) (hdet : u₁.1 * u₂.2 - u₁.2 * u₂.1 ≠ 0) (L : ℝ) :
    ∃ T : ℝ, ∀ y : ℝ × ℝ, T ≤ n.1 * y.1 + n.2 * y.2 →
      ∃ r₀ : ℝ, ∀ r : ℝ, r₀ ≤ r → r ≤ r₀ + L → y + r • w ∈ C := by
  have hn : n ≠ 0 := by
    intro h
    rw [h] at h₁
    simp at h₁
  set α : ℝ := n.1 * u₁.1 + n.2 * u₁.2 with hαdef
  set β : ℝ := n.1 * u₂.1 + n.2 * u₂.2 with hβdef
  set γ : ℝ := n.1 * x₀.1 + n.2 * x₀.2 with hγdef
  have hα0 : α ≠ 0 := h₁.ne'
  have hβ0 : β ≠ 0 := h₂.ne'
  have hαβ : 0 < α * β := mul_pos h₁ h₂
  set q : ℝ × ℝ := β • u₁ - α • u₂ with hqdef
  have hqperp : n.1 * q.1 + n.2 * q.2 = 0 := by
    simp only [hqdef, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      hαdef, hβdef]
    ring
  have hq0 : q ≠ 0 := by
    intro h
    have hq' : β • u₁ - α • u₂ = 0 := by rw [← hqdef]; exact h
    have e1 : β * u₁.1 - α * u₂.1 = 0 := by
      have hc := congrArg Prod.fst hq'
      simpa only [Prod.fst_sub, Prod.smul_fst, smul_eq_mul, Prod.fst_zero] using hc
    have e2 : β * u₁.2 - α * u₂.2 = 0 := by
      have hc := congrArg Prod.snd hq'
      simpa only [Prod.snd_sub, Prod.smul_snd, smul_eq_mul, Prod.snd_zero] using hc
    refine hdet ((mul_eq_zero.mp ?_).resolve_left hβ0)
    show β * (u₁.1 * u₂.2 - u₁.2 * u₂.1) = 0
    linear_combination u₂.2 * e1 - u₂.1 * e2
  obtain ⟨κ, hκ⟩ := exists_smul_of_orthogonal hn hw0 hw hqperp
  have hκ0 : κ ≠ 0 := by
    intro h
    rw [h, zero_smul] at hκ
    exact hq0 hκ
  have hκabs : 0 < |κ| := abs_pos.mpr hκ0
  refine ⟨γ + max 0 (L * α * β / |κ|), fun y hy => ?_⟩
  set d : ℝ := n.1 * y.1 + n.2 * y.2 - γ with hddef
  have hd0 : 0 ≤ d := by
    have := le_max_left (0 : ℝ) (L * α * β / |κ|)
    rw [hddef]
    linarith
  have hdL : L * α * β / |κ| ≤ d := by
    have := le_max_right (0 : ℝ) (L * α * β / |κ|)
    rw [hddef]
    linarith
  -- the two endpoints of the slice of the recession sector at the level of `y`
  have hp₁ : x₀ + (d / α) • u₁ ∈ C :=
    ray_mem_of_forall_add_mem hconv hu₁ hx₀ (div_nonneg hd0 h₁.le)
  have hp₂ : x₀ + (d / β) • u₂ ∈ C :=
    ray_mem_of_forall_add_mem hconv hu₂ hx₀ (div_nonneg hd0 h₂.le)
  have hlev₁ : n.1 * (x₀ + (d / α) • u₁).1 + n.2 * (x₀ + (d / α) • u₁).2
      = n.1 * y.1 + n.2 * y.2 := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have key : n.1 * (x₀.1 + d / α * u₁.1) + n.2 * (x₀.2 + d / α * u₁.2) = γ + d / α * α := by
      rw [hγdef, hαdef]; ring
    rw [key, div_mul_cancel₀ _ hα0, hddef]
    ring
  have hlev₂ : n.1 * (x₀ + (d / β) • u₂).1 + n.2 * (x₀ + (d / β) • u₂).2
      = n.1 * y.1 + n.2 * y.2 := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have key : n.1 * (x₀.1 + d / β * u₂.1) + n.2 * (x₀.2 + d / β * u₂.2) = γ + d / β * β := by
      rw [hγdef, hβdef]; ring
    rw [key, div_mul_cancel₀ _ hβ0, hddef]
    ring
  obtain ⟨r₁, hr₁⟩ := exists_smul_sub_of_level hn hw0 hw hlev₁
  obtain ⟨r₂, hr₂⟩ := exists_smul_sub_of_level hn hw0 hw hlev₂
  -- the two endpoints are `d / (α β)` apart in units of `q = κ • w`
  have e1 : d / (α * β) * β = d / α := by field_simp
  have e2 : d / (α * β) * α = d / β := by field_simp
  have hsub : x₀ + (d / α) • u₁ - (x₀ + (d / β) • u₂) = (d / (α * β)) • q := by
    rw [hqdef, smul_sub, smul_smul, smul_smul, e1, e2]
    abel
  have hgap : r₁ - r₂ = d / (α * β) * κ := by
    rw [hr₁, hr₂, hκ, smul_smul] at hsub
    have hone : (r₁ - r₂) • w = (d / (α * β) * κ) • w := by
      rw [← hsub, sub_smul]
      abel
    have hzero : ((r₁ - r₂) - d / (α * β) * κ) • w = 0 := by rw [sub_smul, hone, sub_self]
    rcases smul_eq_zero.mp hzero with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hw0
  have habs : L ≤ |r₁ - r₂| := by
    have h' : L * α * β ≤ d * |κ| := (div_le_iff₀ hκabs).mp hdL
    rw [hgap, abs_mul, abs_of_nonneg (div_nonneg hd0 hαβ.le), div_mul_eq_mul_div,
      le_div_iff₀ hαβ]
    calc L * (α * β) = L * α * β := by ring
      _ ≤ d * |κ| := h'
  -- the parameter set is an interval containing `r₁` and `r₂`
  have hSconv : Convex ℝ {r : ℝ | y + r • w ∈ C} := by
    intro a ha b hb s t hs ht hst
    show y + (s * a + t * b) • w ∈ C
    have hmem := hconv ha hb hs ht hst
    have hyy : s • y + t • y = y := by rw [← add_smul, hst, one_smul]
    have heq : s • (y + a • w) + t • (y + b • w) = y + (s * a + t * b) • w := by
      calc s • (y + a • w) + t • (y + b • w)
          = (s • y + t • y) + ((s * a) • w + (t * b) • w) := by
            rw [smul_add, smul_add, smul_smul, smul_smul]; abel
        _ = y + (s * a + t * b) • w := by rw [hyy, add_smul]
    rwa [heq] at hmem
  have hSord : {r : ℝ | y + r • w ∈ C}.OrdConnected := hSconv.ordConnected
  have hm₁ : r₁ ∈ {r : ℝ | y + r • w ∈ C} := by
    show y + r₁ • w ∈ C
    rw [← hr₁]
    exact hp₁
  have hm₂ : r₂ ∈ {r : ℝ | y + r • w ∈ C} := by
    show y + r₂ • w ∈ C
    rw [← hr₂]
    exact hp₂
  rcases le_total r₁ r₂ with hle | hle
  · refine ⟨r₁, fun r hra hrb => ?_⟩
    have hgap' : L ≤ r₂ - r₁ := by
      rwa [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ r₂ - r₁)] at habs
    exact hSord.out hm₁ hm₂ ⟨hra, by linarith⟩
  · refine ⟨r₂, fun r hra hrb => ?_⟩
    have hgap' : L ≤ r₁ - r₂ := by
      rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ r₁ - r₂)] at habs
    exact hSord.out hm₂ hm₁ ⟨hra, by linarith⟩

-- Compatibility checks for the intended use at `C := convHullOf R` (add no names to the API).
example (R : Set (ℤ × ℤ)) (hne : (convHullOf R).Nonempty) (w : ℝ × ℝ) :
    w ∈ recCone R ↔ ∃ x ∈ convHullOf R, ∀ t : ℝ, 0 ≤ t → x + t • w ∈ convHullOf R :=
  forall_add_mem_iff_exists_ray_mem (convex_convexHull ℝ _).closure isClosed_closure hne w

example (R : Set (ℤ × ℤ)) {w : ℝ × ℝ} (hw : w ∉ recCone R) (hw' : -w ∉ recCone R) (x : ℝ × ℝ) :
    ∃ N : ℕ, ∀ t : ℝ, (N : ℝ) ≤ |t| → x + t • w ∉ convHullOf R :=
  exists_nat_forall_abs_le_not_mem (convex_convexHull ℝ _).closure isClosed_closure hw hw' x

example (R : Set (ℤ × ℤ)) {x₀ u₁ u₂ w n : ℝ × ℝ} (hx₀ : x₀ ∈ convHullOf R)
    (hu₁ : u₁ ∈ recCone R) (hu₂ : u₂ ∈ recCone R) (hw0 : w ≠ 0)
    (hw : n.1 * w.1 + n.2 * w.2 = 0) (h₁ : 0 < n.1 * u₁.1 + n.2 * u₁.2)
    (h₂ : 0 < n.1 * u₂.1 + n.2 * u₂.2) (hdet : u₁.1 * u₂.2 - u₁.2 * u₂.1 ≠ 0) (L : ℝ) :
    ∃ T : ℝ, ∀ y : ℝ × ℝ, T ≤ n.1 * y.1 + n.2 * y.2 →
      ∃ r₀ : ℝ, ∀ r : ℝ, r₀ ≤ r → r ≤ r₀ + L → y + r • w ∈ convHullOf R :=
  exists_long_window (convex_convexHull ℝ _).closure hx₀ hu₁ hu₂ hw0 hw h₁ h₂ hdet L

/-! ### A window common to a finite family of offsets -/

/-- Cramer's rule in the plane: the coordinates of `g` in a basis `(u₁, u₂)` are the two
quotients of determinants. -/
private lemma cramer_smul_add_smul {u₁ u₂ : ℝ × ℝ} (hdet : u₁.1 * u₂.2 - u₁.2 * u₂.1 ≠ 0)
    (g : ℝ × ℝ) :
    ((g.1 * u₂.2 - g.2 * u₂.1) / (u₁.1 * u₂.2 - u₁.2 * u₂.1)) • u₁ +
      ((u₁.1 * g.2 - u₁.2 * g.1) / (u₁.1 * u₂.2 - u₁.2 * u₂.1)) • u₂ = g := by
  apply Prod.ext <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hdet] <;> ring

/-- `exists_common_window` with the sign of the first coordinate of `w` in the basis `(u₁, u₂)`
fixed to be positive.  The other sign is the same statement with `u₁` and `u₂` swapped. -/
private lemma exists_common_window_aux {C : Set (ℝ × ℝ)} (hconv : Convex ℝ C)
    {x₀ u₁ u₂ w n : ℝ × ℝ} (hx₀ : x₀ ∈ C) (hu₁ : ∀ x ∈ C, x + u₁ ∈ C)
    (hu₂ : ∀ x ∈ C, x + u₂ ∈ C) (hw : n.1 * w.1 + n.2 * w.2 = 0)
    (h₁ : 0 < n.1 * u₁.1 + n.2 * u₁.2) (h₂ : 0 < n.1 * u₂.1 + n.2 * u₂.2)
    (hdet : u₁.1 * u₂.2 - u₁.2 * u₂.1 ≠ 0)
    (hsign : 0 < (w.1 * u₂.2 - w.2 * u₂.1) / (u₁.1 * u₂.2 - u₁.2 * u₂.1))
    {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (p : ι → ℝ × ℝ) (L : ℝ) :
    ∃ T : ℝ, ∀ y : ℝ × ℝ, T ≤ n.1 * y.1 + n.2 * y.2 →
      ∃ r₀ : ℝ, ∀ r : ℝ, r₀ ≤ r → r ≤ r₀ + L → ∀ i ∈ s, y + p i + r • w ∈ C := by
  set α : ℝ := n.1 * u₁.1 + n.2 * u₁.2 with hαdef
  set β : ℝ := n.1 * u₂.1 + n.2 * u₂.2 with hβdef
  set A : ℝ × ℝ → ℝ := fun g => (g.1 * u₂.2 - g.2 * u₂.1) / (u₁.1 * u₂.2 - u₁.2 * u₂.1)
    with hAdef
  set B : ℝ × ℝ → ℝ := fun g => (u₁.1 * g.2 - u₁.2 * g.1) / (u₁.1 * u₂.2 - u₁.2 * u₂.1)
    with hBdef
  have hAadd : ∀ g h : ℝ × ℝ, A (g + h) = A g + A h := fun g h => by
    simp only [hAdef, Prod.fst_add, Prod.snd_add]; ring
  have hBadd : ∀ g h : ℝ × ℝ, B (g + h) = B g + B h := fun g h => by
    simp only [hBdef, Prod.fst_add, Prod.snd_add]; ring
  have hAsmul : ∀ (c : ℝ) (g : ℝ × ℝ), A (c • g) = c * A g := fun c g => by
    simp only [hAdef, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have hBsmul : ∀ (c : ℝ) (g : ℝ × ℝ), B (c • g) = c * B g := fun c g => by
    simp only [hBdef, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have hlevel : ∀ g : ℝ × ℝ, A g * α + B g * β = n.1 * g.1 + n.2 * g.2 := fun g => by
    simp only [hAdef, hBdef, hαdef, hβdef]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hdet]
    ring
  have hcramer : ∀ g : ℝ × ℝ, x₀ + A g • u₁ + B g • u₂ = x₀ + g := fun g => by
    rw [add_assoc]
    congr 1
    simp only [hAdef, hBdef]
    exact cramer_smul_add_smul hdet g
  have hmem : ∀ g : ℝ × ℝ, 0 ≤ A g → 0 ≤ B g → x₀ + g ∈ C := fun g hA hB => by
    have hcomb := add_recession_pair_mem hconv hu₁ hu₂ hx₀ hA hB
    rwa [hcramer g] at hcomb
  set γ₁ : ℝ := A w with hγ₁def
  set γ₂ : ℝ := B w with hγ₂def
  have hγ₁pos : 0 < γ₁ := by rw [hγ₁def]; simp only [hAdef]; exact hsign
  have hγ : γ₁ * α + γ₂ * β = 0 := by rw [hγ₁def, hγ₂def, hlevel w]; exact hw
  have hγ₂neg : γ₂ < 0 := by
    by_contra hcon
    have hprod : 0 ≤ γ₂ * β := mul_nonneg (not_lt.mp hcon) h₂.le
    have hpos : 0 < γ₁ * α := mul_pos hγ₁pos h₁
    linarith
  set P : ℝ := s.sup' hs (fun i => A (p i)) with hPdef
  set Q : ℝ := s.inf' hs (fun i => A (p i)) with hQdef
  set S : ℝ := s.inf' hs (fun i => n.1 * (p i).1 + n.2 * (p i).2) with hSdef
  refine ⟨n.1 * x₀.1 + n.2 * x₀.2 + L * γ₁ * α + α * (P - Q) - S, fun y hy => ?_⟩
  refine ⟨-(A (y - x₀) + Q) / γ₁, fun r hrl hru i hi => ?_⟩
  have hAP : A (p i) ≤ P := by rw [hPdef]; exact Finset.le_sup' (fun i => A (p i)) hi
  have hQA : Q ≤ A (p i) := by rw [hQdef]; exact Finset.inf'_le (fun i => A (p i)) hi
  have hSn : S ≤ n.1 * (p i).1 + n.2 * (p i).2 := by
    rw [hSdef]
    exact Finset.inf'_le (fun i => n.1 * (p i).1 + n.2 * (p i).2) hi
  have hlevi : (A (y - x₀) + A (p i)) * α + (B (y - x₀) + B (p i)) * β
      = n.1 * y.1 + n.2 * y.2 + (n.1 * (p i).1 + n.2 * (p i).2)
        - (n.1 * x₀.1 + n.2 * x₀.2) := by
    have hh := hlevel (y - x₀ + p i)
    rw [hAadd, hBadd] at hh
    rw [hh]
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
    ring
  have hxg : x₀ + (y - x₀ + (p i + r • w)) = y + p i + r • w := by abel
  have hAg : A (y - x₀ + (p i + r • w)) = A (y - x₀) + A (p i) + r * γ₁ := by
    rw [hAadd, hAadd, hAsmul, ← hγ₁def]; ring
  have hBg : B (y - x₀ + (p i + r • w)) = B (y - x₀) + B (p i) + r * γ₂ := by
    rw [hBadd, hBadd, hBsmul, ← hγ₂def]; ring
  rw [← hxg]
  refine hmem _ ?_ ?_
  · rw [hAg]
    have hlow : -(A (y - x₀) + Q) ≤ r * γ₁ := (div_le_iff₀ hγ₁pos).mp hrl
    linarith
  · rw [hBg]
    have hPA : 0 ≤ α * (P - A (p i)) := mul_nonneg h₁.le (by linarith)
    have hmain : 0 ≤ (B (y - x₀) + B (p i)) * β + (A (y - x₀) + Q) * α - L * γ₁ * α := by
      linarith
    have hstep : (-(A (y - x₀) + Q) / γ₁ + L) * γ₂ ≤ r * γ₂ :=
      mul_le_mul_of_nonpos_right hru hγ₂neg.le
    have hkey : 0 ≤ B (y - x₀) + B (p i) + (-(A (y - x₀) + Q) / γ₁ + L) * γ₂ := by
      by_contra hcon
      have hneg : B (y - x₀) + B (p i) + (-(A (y - x₀) + Q) / γ₁ + L) * γ₂ < 0 :=
        not_le.mp hcon
      have hmul : (B (y - x₀) + B (p i) + (-(A (y - x₀) + Q) / γ₁ + L) * γ₂) * (γ₁ * β) < 0 :=
        mul_neg_of_neg_of_pos hneg (mul_pos hγ₁pos h₂)
      have hcancel : -(A (y - x₀) + Q) / γ₁ * γ₁ = -(A (y - x₀) + Q) :=
        div_mul_cancel₀ _ hγ₁pos.ne'
      have hid : (B (y - x₀) + B (p i) + (-(A (y - x₀) + Q) / γ₁ + L) * γ₂) * (γ₁ * β)
          = γ₁ * ((B (y - x₀) + B (p i)) * β + (A (y - x₀) + Q) * α - L * γ₁ * α) := by
        calc (B (y - x₀) + B (p i) + (-(A (y - x₀) + Q) / γ₁ + L) * γ₂) * (γ₁ * β)
            = ((B (y - x₀) + B (p i)) * γ₁ + -(A (y - x₀) + Q) / γ₁ * γ₁ * γ₂
                + L * γ₂ * γ₁) * β := by ring
          _ = ((B (y - x₀) + B (p i)) * γ₁ + -(A (y - x₀) + Q) * γ₂ + L * γ₂ * γ₁) * β := by
                rw [hcancel]
          _ = γ₁ * ((B (y - x₀) + B (p i)) * β + (A (y - x₀) + Q) * α - L * γ₁ * α) := by
                linear_combination (L * γ₁ - (A (y - x₀) + Q)) * hγ
      rw [hid] at hmul
      have hnn := mul_nonneg hγ₁pos.le hmain
      linarith
    linarith

/-- **A window common to a finite family of offsets.**

Let `u₁, u₂` be recession directions of the convex set `C`, linearly independent and both on the
positive side of the linear form `y ↦ ⟨n, y⟩`, and let `w ≠ 0` span `ker ⟨n, ·⟩`, so that the
level sets of `⟨n, ·⟩` are exactly the lines `y + ℝ w`.  Given a finite family of offsets
`p i` and a prescribed length `L`, all sufficiently high level lines carry an interval of
length `L` which works for *every* offset simultaneously: there is a threshold `T` such that
every `y` with `⟨n, y⟩ ≥ T` admits `r₀` with `y + p i + r • w ∈ C` for all `i` and all
`r ∈ [r₀, r₀ + L]`.

This strengthens `exists_long_window` (the case of a single offset `0`) in exactly the way its
consumers need: shifting `y` by `p i` moves the window by an amount depending only on `p i`,
never on `y`, while the window itself grows linearly in `⟨n, y⟩`, so a common sub-window of
any prescribed length survives.

Proof: writing `g = A g • u₁ + B g • u₂` in the basis `(u₁, u₂)`, membership of `x₀ + g` in the
sector `x₀ + ℝ₊u₁ + ℝ₊u₂ ⊆ C` is the pair of inequalities `A g ≥ 0`, `B g ≥ 0`, both affine in
`r` with slopes `A w` and `B w` of opposite signs (their `⟨n, ·⟩`-weighted sum vanishes).  The
resulting window has length `⟨n, y - x₀⟩ / (A w · ⟨n, u₁⟩)` and left endpoint `-A (y - x₀ + p i)
/ A w`; the endpoints for different `i` differ by constants. -/
theorem exists_common_window {C : Set (ℝ × ℝ)} (hconv : Convex ℝ C) {x₀ u₁ u₂ w n : ℝ × ℝ}
    (hx₀ : x₀ ∈ C) (hu₁ : ∀ x ∈ C, x + u₁ ∈ C) (hu₂ : ∀ x ∈ C, x + u₂ ∈ C) (hw0 : w ≠ 0)
    (hw : n.1 * w.1 + n.2 * w.2 = 0) (h₁ : 0 < n.1 * u₁.1 + n.2 * u₁.2)
    (h₂ : 0 < n.1 * u₂.1 + n.2 * u₂.2) (hdet : u₁.1 * u₂.2 - u₁.2 * u₂.1 ≠ 0)
    {ι : Type*} (s : Finset ι) (p : ι → ℝ × ℝ) (L : ℝ) :
    ∃ T : ℝ, ∀ y : ℝ × ℝ, T ≤ n.1 * y.1 + n.2 * y.2 →
      ∃ r₀ : ℝ, ∀ r : ℝ, r₀ ≤ r → r ≤ r₀ + L → ∀ i ∈ s, y + p i + r • w ∈ C := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨0, fun _ _ => ⟨0, fun _ _ _ i hi => absurd hi (by simp)⟩⟩
  set γ₁ : ℝ := (w.1 * u₂.2 - w.2 * u₂.1) / (u₁.1 * u₂.2 - u₁.2 * u₂.1) with hγ₁def
  set γ₂ : ℝ := (u₁.1 * w.2 - u₁.2 * w.1) / (u₁.1 * u₂.2 - u₁.2 * u₂.1) with hγ₂def
  have hwdecomp : γ₁ • u₁ + γ₂ • u₂ = w := by
    rw [hγ₁def, hγ₂def]; exact cramer_smul_add_smul hdet w
  have hγ : γ₁ * (n.1 * u₁.1 + n.2 * u₁.2) + γ₂ * (n.1 * u₂.1 + n.2 * u₂.2) = 0 := by
    have hh := congrArg (fun y : ℝ × ℝ => n.1 * y.1 + n.2 * y.2) hwdecomp
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hh
    rw [hw] at hh
    linear_combination hh
  have hγ₁ne : γ₁ ≠ 0 := by
    intro h0
    have hγ₂0 : γ₂ = 0 := by
      rw [h0, zero_mul, zero_add] at hγ
      exact (mul_eq_zero.mp hγ).resolve_right h₂.ne'
    exact hw0 (by rw [← hwdecomp, h0, hγ₂0, zero_smul, zero_smul, add_zero])
  rcases lt_or_gt_of_ne hγ₁ne with hneg | hpos
  · have hprodpos : 0 < γ₂ * (n.1 * u₂.1 + n.2 * u₂.2) := by
      have hh : 0 < -γ₁ * (n.1 * u₁.1 + n.2 * u₁.2) := mul_pos (neg_pos.mpr hneg) h₁
      linarith
    have hγ₂pos : 0 < γ₂ := by
      by_contra hcon
      have hh : 0 ≤ -γ₂ * (n.1 * u₂.1 + n.2 * u₂.2) :=
        mul_nonneg (neg_nonneg.mpr (not_lt.mp hcon)) h₂.le
      linarith
    have hdet' : u₂.1 * u₁.2 - u₂.2 * u₁.1 ≠ 0 := fun h0 => hdet (by linarith)
    refine exists_common_window_aux hconv hx₀ hu₂ hu₁ hw h₂ h₁ hdet' ?_ hs p L
    rw [show w.1 * u₁.2 - w.2 * u₁.1 = -(u₁.1 * w.2 - u₁.2 * w.1) by ring,
      show u₂.1 * u₁.2 - u₂.2 * u₁.1 = -(u₁.1 * u₂.2 - u₁.2 * u₂.1) by ring, neg_div_neg_eq,
      ← hγ₂def]
    exact hγ₂pos
  · refine exists_common_window_aux hconv hx₀ hu₁ hu₂ hw h₁ h₂ hdet ?_ hs p L
    rw [← hγ₁def]
    exact hpos

/-! ### The quantitative recession criterion for a lattice-convex region -/

/-- **Every line parallel to `v` far enough out on the `ε π_v`-side meets the region, and meets
it in a window long enough to contain a multiple of `k • v` together with finitely many
offsets.**  Paper Proposition 8.9(b), case (β).

`R` is a non-empty lattice-convex region whose recession cone has non-empty interior (in §8.3
this comes from `mem_interior_recCone`, i.e. from the two independent periods of the fully
periodic background) and lies in the half-plane `{ε π_v ≥ 0}`.  Then there is a threshold `t₀`
such that every lattice point `z` with `ε π_v z ≥ t₀` can be translated *along `v` itself* into
`R`, by an integer multiple of `k • v`, simultaneously for every member of a prescribed finite
family of offsets `p i`.

The translation direction matters: `ε π_v` is constant along `v` (as `π_v v = 0`), so the
conclusion is a statement about the level line of `z`, and the consumer transports it back to
`z` using a period of the field it is studying.  The naive strengthening "`z ∈ R` itself" is
**false**: take `R` the lattice points of the first quadrant, `v := (1, 0)` and `ε := +`, so
that `recCone R` is the quadrant, `ε π_v = z.2 ≥ 0` on it and the line `ℝ v` misses its
interior, yet `(-1, t) ∉ R` for every `t`.  What is true, and what this lemma says, is that
`(-1 + N, t) ∈ R` for large `N`. -/
theorem exists_forall_ge_piE_exists_zsmul_add_mem {R : Set (ℤ × ℤ)}
    (hR : IsLatticeConvexRegion R) (hRne : R.Nonempty)
    (hint : (interior (recCone R)).Nonempty) {v : ℤ × ℤ} (hv : v ≠ 0) {ε : Bool}
    (hε : ∀ y ∈ recCone R, 0 ≤ piER ε v y) {k : ℤ} (hk : 0 < k)
    {ι : Type*} [Fintype ι] (p : ι → ℤ × ℤ) :
    ∃ t₀ : ℤ, ∀ z : ℤ × ℤ, t₀ ≤ piE ε v z → ∃ N : ℤ, ∀ i : ι, z + N • (k • v) + p i ∈ R := by
  classical
  -- `n` is the normal of the half-plane `{ε π_v ≥ 0}`, and `w = v` spans its boundary line.
  obtain ⟨σ, hσ1, hσ⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ y : ℝ × ℝ, piER ε v y = σ * piR v y := by
    cases ε
    · exact ⟨-1, Or.inr rfl, fun y => by simp [piER]⟩
    · exact ⟨1, Or.inl rfl, fun y => by simp [piER]⟩
  have hσsq : σ * σ = 1 := by rcases hσ1 with h | h <;> rw [h] <;> norm_num
  set n : ℝ × ℝ := (-(σ * (v.2 : ℝ)), σ * (v.1 : ℝ)) with hndef
  set w : ℝ × ℝ := toReal v with hwdef
  have hn_eq : ∀ y : ℝ × ℝ, n.1 * y.1 + n.2 * y.2 = piER ε v y := fun y => by
    rw [hσ y, hndef]
    simp only [piR]
    ring
  have hw0 : w ≠ 0 := by
    intro h0
    refine hv (Prod.ext ?_ ?_)
    · have hh := congrArg Prod.fst h0
      simpa [hwdef, toReal] using hh
    · have hh := congrArg Prod.snd h0
      simpa [hwdef, toReal] using hh
  have hwperp : n.1 * w.1 + n.2 * w.2 = 0 := by
    have hzero : piE ε v v = 0 := by cases ε <;> simp [piE, pi]
    rw [hn_eq w, hwdef, piER_toReal, hzero]
    norm_num
  have hvne : (v.1 : ℝ) ≠ 0 ∨ (v.2 : ℝ) ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    exact hv (Prod.ext (by exact_mod_cast hcon.1) (by exact_mod_cast hcon.2))
  have hnsq : 0 < n.1 * n.1 + n.2 * n.2 := by
    have hval : n.1 * n.1 + n.2 * n.2 = (v.1 : ℝ) * (v.1 : ℝ) + (v.2 : ℝ) * (v.2 : ℝ) := by
      simp only [hndef]
      linear_combination ((v.1 : ℝ) * (v.1 : ℝ) + (v.2 : ℝ) * (v.2 : ℝ)) * hσsq
    rw [hval]
    rcases hvne with h | h
    · have h1 : 0 < (v.1 : ℝ) * (v.1 : ℝ) := mul_self_pos.mpr h
      have h2 : 0 ≤ (v.2 : ℝ) * (v.2 : ℝ) := mul_self_nonneg _
      linarith
    · have h1 : 0 ≤ (v.1 : ℝ) * (v.1 : ℝ) := mul_self_nonneg _
      have h2 : 0 < (v.2 : ℝ) * (v.2 : ℝ) := mul_self_pos.mpr h
      linarith
  -- An interior direction of the recession cone is strictly on the positive side.
  obtain ⟨w₀, hw₀int⟩ := hint
  obtain ⟨δ, hδpos, hball⟩ := Metric.isOpen_iff.mp isOpen_interior w₀ hw₀int
  have hballmem : ∀ y : ℝ × ℝ, dist y w₀ < δ → y ∈ recCone R := fun y hy =>
    interior_subset (hball (Metric.mem_ball.mpr hy))
  have hw₀nonneg : 0 ≤ n.1 * w₀.1 + n.2 * w₀.2 := by
    rw [hn_eq w₀]; exact hε w₀ (interior_subset hw₀int)
  have hw₀pos : 0 < n.1 * w₀.1 + n.2 * w₀.2 := by
    rcases hw₀nonneg.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      set t : ℝ := δ / (2 * (‖n‖ + 1)) with htdef
      have hnn : (0 : ℝ) ≤ ‖n‖ := norm_nonneg n
      have htpos : 0 < t := by rw [htdef]; positivity
      have hb : t * (‖n‖ + 1) = δ / 2 := by
        rw [htdef]
        field_simp
      have hdist : dist (w₀ - t • n) w₀ < δ := by
        rw [dist_eq_norm, show w₀ - t • n - w₀ = -(t • n) by abel, norm_neg, norm_smul,
          Real.norm_eq_abs, abs_of_pos htpos]
        have hle : t * ‖n‖ ≤ t * (‖n‖ + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) htpos.le
        linarith
      have hh := hε _ (hballmem _ hdist)
      rw [← hn_eq] at hh
      have hexp : n.1 * (w₀ - t • n).1 + n.2 * (w₀ - t • n).2
          = n.1 * w₀.1 + n.2 * w₀.2 - t * (n.1 * n.1 + n.2 * n.2) := by
        simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
      rw [hexp, ← heq] at hh
      have := mul_pos htpos hnsq
      linarith
  -- Two independent recession directions on that side, obtained by tilting `w₀` along `±w`.
  set c : ℝ := δ / (2 * (‖w‖ + 1)) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hcnorm : c * ‖w‖ < δ := by
    have hb : c * (‖w‖ + 1) = δ / 2 := by
      rw [hcdef]
      field_simp
    have hle : c * ‖w‖ ≤ c * (‖w‖ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [norm_nonneg w]) hcpos.le
    linarith
  have hu₁mem : w₀ + c • w ∈ recCone R := by
    refine hballmem _ ?_
    rw [dist_eq_norm, show w₀ + c • w - w₀ = c • w by abel, norm_smul, Real.norm_eq_abs,
      abs_of_pos hcpos]
    exact hcnorm
  have hu₂mem : w₀ - c • w ∈ recCone R := by
    refine hballmem _ ?_
    rw [dist_eq_norm, show w₀ - c • w - w₀ = -(c • w) by abel, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_pos hcpos]
    exact hcnorm
  have hlev₁ : 0 < n.1 * (w₀ + c • w).1 + n.2 * (w₀ + c • w).2 := by
    have hval : n.1 * (w₀ + c • w).1 + n.2 * (w₀ + c • w).2 = n.1 * w₀.1 + n.2 * w₀.2 := by
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      linear_combination c * hwperp
    rw [hval]; exact hw₀pos
  have hlev₂ : 0 < n.1 * (w₀ - c • w).1 + n.2 * (w₀ - c • w).2 := by
    have hval : n.1 * (w₀ - c • w).1 + n.2 * (w₀ - c • w).2 = n.1 * w₀.1 + n.2 * w₀.2 := by
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      linear_combination (-c) * hwperp
    rw [hval]; exact hw₀pos
  have hdetu : (w₀ + c • w).1 * (w₀ - c • w).2 - (w₀ + c • w).2 * (w₀ - c • w).1 ≠ 0 := by
    have hrel : w.1 * w₀.2 - w.2 * w₀.1 = σ * (n.1 * w₀.1 + n.2 * w₀.2) := by
      simp only [hndef, hwdef, toReal]
      linear_combination (-((v.1 : ℝ) * w₀.2 - (v.2 : ℝ) * w₀.1)) * hσsq
    have hval : (w₀ + c • w).1 * (w₀ - c • w).2 - (w₀ + c • w).2 * (w₀ - c • w).1
        = 2 * c * (w.1 * w₀.2 - w.2 * w₀.1) := by
      simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]
      ring
    have hσne : σ ≠ 0 := by rcases hσ1 with h | h <;> rw [h] <;> norm_num
    rw [hval, hrel]
    exact mul_ne_zero (by positivity) (mul_ne_zero hσne hw₀pos.ne')
  -- The window lemma, applied to `C = C_R` with the finite family of offsets.
  obtain ⟨z₀, hz₀⟩ := hRne
  have hx₀mem : toReal z₀ ∈ convHullOf R := by
    have hpre := eq_preimage_convHullOf hR
    rw [hpre] at hz₀
    exact hz₀
  obtain ⟨T, hT⟩ := exists_common_window (C := convHullOf R) (convex_convexHull ℝ _).closure
    hx₀mem hu₁mem hu₂mem hw0 hwperp hlev₁ hlev₂ hdetu (Finset.univ : Finset ι)
    (fun i => toReal (p i)) ((k : ℝ))
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  refine ⟨⌈T⌉, fun z hz => ?_⟩
  have hlevz : T ≤ n.1 * (toReal z).1 + n.2 * (toReal z).2 := by
    rw [hn_eq, piER_toReal]
    have h1 : T ≤ (⌈T⌉ : ℝ) := Int.le_ceil T
    have h2 : ((⌈T⌉ : ℤ) : ℝ) ≤ ((piE ε v z : ℤ) : ℝ) := by exact_mod_cast hz
    linarith
  obtain ⟨r₀, hr₀⟩ := hT (toReal z) hlevz
  refine ⟨⌈r₀ / (k : ℝ)⌉, fun i => ?_⟩
  have hlow : r₀ ≤ ((⌈r₀ / (k : ℝ)⌉ : ℤ) : ℝ) * (k : ℝ) :=
    (div_le_iff₀ hkR).mp (Int.le_ceil (r₀ / (k : ℝ)))
  have hhigh : ((⌈r₀ / (k : ℝ)⌉ : ℤ) : ℝ) * (k : ℝ) ≤ r₀ + (k : ℝ) := by
    have hh := mul_lt_mul_of_pos_right (Int.ceil_lt_add_one (r₀ / (k : ℝ))) hkR
    rw [add_mul, div_mul_cancel₀ _ hkR.ne', one_mul] at hh
    linarith
  have hmem := hr₀ (((⌈r₀ / (k : ℝ)⌉ : ℤ) : ℝ) * (k : ℝ)) hlow hhigh i (Finset.mem_univ i)
  have hgoal : toReal (z + (⌈r₀ / (k : ℝ)⌉ : ℤ) • (k • v) + p i)
      = toReal z + toReal (p i) + (((⌈r₀ / (k : ℝ)⌉ : ℤ) : ℝ) * (k : ℝ)) • w := by
    rw [toReal_add, toReal_add, toReal_zsmul, toReal_zsmul, smul_smul, ← hwdef]
    abel
  rw [eq_preimage_convHullOf hR]
  show toReal (z + (⌈r₀ / (k : ℝ)⌉ : ℤ) • (k • v) + p i) ∈ convHullOf R
  rw [hgoal]
  exact hmem

-- Compatibility check for the intended use in §8.3, case (β): the index type is the `2 ^ m'`
-- subsets of `Fin m'` and the offsets are the partial sums of `H` (adds no name to the API).
example {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R) (hRne : R.Nonempty)
    (hint : (interior (recCone R)).Nonempty) {v : ℤ × ℤ} (hv : v ≠ 0) {ε : Bool}
    (hε : ∀ y ∈ recCone R, 0 ≤ piER ε v y) {k : ℕ} (hk : 0 < k) {m' : ℕ} (H : Fin m' → ℤ × ℤ) :
    ∃ t : ℤ, ∀ z : ℤ × ℤ, t ≤ piE ε v z →
      ∃ N : ℤ, ∀ C : Finset (Fin m'), z + N • ((k : ℤ) • v) + ∑ l ∈ C, H l ∈ R :=
  exists_forall_ge_piE_exists_zsmul_add_mem hR hRne hint hv hε (by exact_mod_cast hk)
    (fun C : Finset (Fin m') => ∑ l ∈ C, H l)

end Nivat