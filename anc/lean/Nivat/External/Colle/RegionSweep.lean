/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Lemma41
import Nivat.External.Colle.Claim43
import Nivat.Lattice.Primitive
import Nivat.Section8.RegionUpgrade

/-!
# Sweep stability of `Colle41.IsRegion`

Collé's outer chain (`b3_colle2.txt:806-812`) is built by *sweeping*:
`𝓡_i := {g + t·v_{ℓ_i} : g ∈ 𝓡_{i+1}, t ∈ ℤ₊}`.  The tree so far only knows that a
region survives a half-plane *cut* (`LE2.isRegion_inter_halfPlaneLE`, `RegionCut.lean:334`;
`LE2.isRegion_inter_halfPlaneGE`, `RegionCutGE.lean:61`).  This file supplies the sweep.

## The honest hypothesis on `w`

`Colle41.IsRegion K u u'` (`Lemma41.lean:688`) is `IsLatticeConvexRegion K` plus a `u`-ray and
a `u'`-ray.  The two rays are monotone in `K`, so they survive any sweep for free
(`rayIn_sweep_of_rayIn`); the whole content is lattice convexity, and **that is false for a
general primitive `w`**:

* `C = {(0,0), (1,2)}` is lattice-convex (the segment has no interior lattice point) and
  `w = (1,0)` is primitive, but `sweep C w ∋ (0,0), (2,2)` misses their midpoint `(1,1)`
  (`not_isLatticeConvexRegion_sweep_pair`).
* `C = {0}`, `w = (2,0)`: the sweep `{(2t,0)}` misses `(1,0)` — primitivity is needed too
  (`not_isLatticeConvexRegion_sweep_two`).

The exact condition (necessary and sufficient given `Primitive w`) is that the `w`-levels
`det w c`, `c ∈ C`, form an interval of `ℤ` — no lattice line parallel to `w` meets `conv C`
without meeting `C`.  That is `LevelInterval C w` below.  Nothing relates `w` to `u, u'`.

## Proof route

The witness closed convex set for the sweep is the intersection of *all* closed convex subsets
of `ℝ²` containing it (closed and convex for free).  A lattice point `z` outside the sweep is
excluded by one explicit closed half-plane:

* if the level `det w z` is not attained on `C`, `LevelInterval` puts every level of `C` on one
  side of it, and the level half-plane `{det w · ≤ det w z − 1}` (or `≥ … + 1`) contains the
  sweep (levels are `+w`-invariant);
* if the level is attained by `c₀ ∈ C`, then `c₀ = z + k•w` with `k ∈ ℤ` (`Primitive w`),
  `k > 0` since `z ∉ sweep`, and `z ∉ C`.  Hahn–Banach separates `toReal z` from `C`'s closed
  convex witness by `f`; `f c₀ < u < f z` with `c₀ = z + k w`, `k > 0`, forces `f w < 0`, so
  `{f ≤ u}` is automatically `+w`-recessive and contains the sweep.

No recession-cone or closure analysis is needed.

## Transversality is not enough (hand-read, **not compiled** — PROTOCOL §15; no consumer, §20)

`det u' w ≠ 0` does not replace `LevelInterval`: take `C = ℕ • (1, 2)` (lattice points of a
closed ray, so lattice-convex), `u = u' = (1, 2)`, `w = (1, 0)`.  Then `det u' w = -2 ≠ 0` and
`w` is primitive, but `sweep C w ∋ (0,0), (2,2)` while `(1,1) ∉ sweep C w` (it would need
`2t = 1`).  The `det w`-levels of `C` are `2ℕ`; that gap is what `LevelInterval` measures.

## Iteration

`sweep` is idempotent in a fixed direction (`sweep_sweep_self`) — iterating the *same* `w`
never grows the set, which is the obstruction `L1RegionBuild.lean`'s docstring records.  For a
chain with changing directions, `LevelInterval` propagates unconditionally when consecutive
directions are unimodular (`levelInterval_sweep_of_det_eq_one` / `_neg_one`), and **fails**
otherwise: `sweep (sweep {0} (2,1)) (0,1)` — the `wedgeRinf B vl u'` shape with `B = {0}`,
`det (0,1) (2,1) = -2` — is not lattice-convex (`not_isLatticeConvexRegion_sweep_sweep_two_one`).
-/

set_option autoImplicit false

open Nivat

namespace Nivat.RegionSweep

/-! ## §1  The sweep and its elementary properties -/

/-- `C` swept forward by `w`: `{g + t•w : g ∈ C, t ∈ ℕ}` (Collé's `{g + t v⃗_ℓ : t ∈ ℤ₊}`). -/
def sweep (C : Set (ℤ × ℤ)) (w : ℤ × ℤ) : Set (ℤ × ℤ) :=
  {z | ∃ g ∈ C, ∃ t : ℕ, z = g + (t : ℤ) • w}

theorem mem_sweep {C : Set (ℤ × ℤ)} {w z : ℤ × ℤ} :
    z ∈ sweep C w ↔ ∃ g ∈ C, ∃ t : ℕ, z = g + (t : ℤ) • w := Iff.rfl

theorem add_nsmul_mem_sweep {C : Set (ℤ × ℤ)} {w g : ℤ × ℤ} (hg : g ∈ C) (t : ℕ) :
    g + (t : ℤ) • w ∈ sweep C w :=
  ⟨g, hg, t, rfl⟩

/-- Monotonicity: `C ⊆ sweep C w` (take `t = 0`). -/
theorem subset_sweep (C : Set (ℤ × ℤ)) (w : ℤ × ℤ) : C ⊆ sweep C w :=
  fun g hg => ⟨g, hg, 0, by simp⟩

theorem sweep_mono {C D : Set (ℤ × ℤ)} (h : C ⊆ D) (w : ℤ × ℤ) : sweep C w ⊆ sweep D w :=
  fun _ ⟨g, hg, t, ht⟩ => ⟨g, h hg, t, ht⟩

/-- The sweep is `+w`-closed. -/
theorem add_mem_sweep {C : Set (ℤ × ℤ)} {w z : ℤ × ℤ} (hz : z ∈ sweep C w) :
    z + w ∈ sweep C w := by
  obtain ⟨g, hg, t, rfl⟩ := hz
  refine ⟨g, hg, t + 1, ?_⟩
  push_cast
  rw [add_smul, one_smul, add_assoc]

/-- Every point of `C` starts a `w`-ray inside the sweep. -/
theorem rayIn_sweep_of_mem {C : Set (ℤ × ℤ)} {w g : ℤ × ℤ} (hg : g ∈ C) :
    Colle41.RayIn (sweep C w) g w :=
  fun k => ⟨g, hg, k, rfl⟩

/-- Rays of `C` survive the sweep (in any direction `v`, for any `w`). -/
theorem rayIn_sweep_of_rayIn {C : Set (ℤ × ℤ)} {w z₀ v : ℤ × ℤ} (h : Colle41.RayIn C z₀ v) :
    Colle41.RayIn (sweep C w) z₀ v :=
  fun k => subset_sweep C w (h k)

/-- **Idempotence.**  Sweeping twice in the same direction is sweeping once; a chain
`C (n+1) := sweep (C n) w` with a *fixed* `w` is constant from `n = 1` on. -/
theorem sweep_sweep_self (C : Set (ℤ × ℤ)) (w : ℤ × ℤ) : sweep (sweep C w) w = sweep C w := by
  ext z
  constructor
  · rintro ⟨_, ⟨g, hg, s, rfl⟩, t, rfl⟩
    refine ⟨g, hg, s + t, ?_⟩
    push_cast
    rw [add_smul, add_assoc]
  · exact fun h => subset_sweep _ _ h

/-- Sweeps in two directions commute. -/
theorem sweep_sweep_comm (C : Set (ℤ × ℤ)) (w w' : ℤ × ℤ) :
    sweep (sweep C w) w' = sweep (sweep C w') w := by
  ext z
  constructor
  · rintro ⟨_, ⟨g, hg, s, rfl⟩, t, rfl⟩
    exact ⟨g + (t : ℤ) • w', ⟨g, hg, t, rfl⟩, s, by abel⟩
  · rintro ⟨_, ⟨g, hg, s, rfl⟩, t, rfl⟩
    exact ⟨g + (t : ℤ) • w, ⟨g, hg, t, rfl⟩, s, by abel⟩

/-- **Strictness, honestly.**  `C ⊂ sweep C w` iff `C` is not already `+w`-closed.  There is no
unconditional strictness: a `+w`-closed `C` (e.g. the sweep itself, by `add_mem_sweep`) equals
its sweep. -/
theorem ssubset_sweep_iff (C : Set (ℤ × ℤ)) (w : ℤ × ℤ) :
    C ⊂ sweep C w ↔ ∃ g ∈ C, g + w ∉ C := by
  rw [ssubset_iff_subset_not_subset]
  constructor
  · rintro ⟨-, hns⟩
    by_contra hcon
    push Not at hcon
    apply hns
    rintro _ ⟨g, hg, t, rfl⟩
    induction t with
    | zero => simpa using hg
    | succ n ih =>
        have h := hcon _ ih
        push_cast
        rwa [add_smul, one_smul, ← add_assoc]
  · rintro ⟨g, hg, hgw⟩
    refine ⟨subset_sweep C w, fun hsub => hgw (hsub ⟨g, hg, 1, by simp⟩)⟩

/-- `sweep C w = C` exactly when `C` is `+w`-closed. -/
theorem sweep_eq_self_iff (C : Set (ℤ × ℤ)) (w : ℤ × ℤ) :
    sweep C w = C ↔ ∀ g ∈ C, g + w ∈ C := by
  constructor
  · intro h g hg
    rw [← h]
    exact add_mem_sweep (subset_sweep C w hg)
  · intro h
    refine Set.Subset.antisymm ?_ (subset_sweep C w)
    intro z hz
    by_contra hzC
    have hss : C ⊂ sweep C w := ⟨subset_sweep C w, fun hsub => hzC (hsub hz)⟩
    obtain ⟨g, hg, hgw⟩ := (ssubset_sweep_iff C w).mp hss
    exact hgw (h g hg)

/-! ## §2  The level condition -/

/-- **The `w`-levels of `C` form an interval of `ℤ`.**  Every integer between two attained
values of `det w ·` on `C` is attained.  Equivalently (for primitive `w`): every lattice line
parallel to `w` that meets `conv C` meets `C`.  This is the exact extra hypothesis under which
sweeping by `w` preserves lattice convexity. -/
def LevelInterval (C : Set (ℤ × ℤ)) (w : ℤ × ℤ) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, ∀ m : ℤ, det w a ≤ m → m ≤ det w b → ∃ c ∈ C, det w c = m

/-- Levels are `+w`-invariant. -/
theorem det_add_zsmul_self (w g : ℤ × ℤ) (t : ℤ) : det w (g + t • w) = det w g := by
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The real level functional `⟨(−w₂, w₁), ·⟩`, extending `det w` to `ℝ²`. -/
def rlevel (w : ℤ × ℤ) (p : ℝ × ℝ) : ℝ := (w.1 : ℝ) * p.2 - (w.2 : ℝ) * p.1

theorem rlevel_toReal (w z : ℤ × ℤ) : rlevel w (toReal z) = (det w z : ℝ) := by
  simp only [rlevel, toReal, det]
  push_cast
  ring

theorem isLinearMap_rlevel (w : ℤ × ℤ) : IsLinearMap ℝ (rlevel w) := by
  constructor
  · intro x y
    simp only [rlevel, Prod.fst_add, Prod.snd_add]
    ring
  · intro c x
    simp only [rlevel, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring

theorem continuous_rlevel (w : ℤ × ℤ) : Continuous (rlevel w) := by
  unfold rlevel
  fun_prop

/-- Level sets of the sweep are `+w`-invariant: the level of `g + t•w` is that of `g`. -/
theorem rlevel_toReal_mem_sweep {C : Set (ℤ × ℤ)} {w z : ℤ × ℤ} (hz : z ∈ sweep C w) :
    ∃ g ∈ C, rlevel w (toReal z) = (det w g : ℝ) := by
  obtain ⟨g, hg, t, rfl⟩ := hz
  exact ⟨g, hg, by rw [rlevel_toReal, det_add_zsmul_self]⟩

/-! ## §3  Sweep stability -/

/-- **Lattice convexity survives a sweep** by a primitive `w` whose levels on `C` form an
interval.  See the module docstring for why both hypotheses are needed and for the route. -/
theorem isLatticeConvexRegion_sweep {C : Set (ℤ × ℤ)} {w : ℤ × ℤ}
    (hC : IsLatticeConvexRegion C) (hw : Primitive w) (hlev : LevelInterval C w) :
    IsLatticeConvexRegion (sweep C w) := by
  classical
  -- The witness: every closed convex superset of the (real image of the) sweep.
  set 𝒟 : Set (Set (ℝ × ℝ)) :=
    {D | Convex ℝ D ∧ IsClosed D ∧ toReal '' sweep C w ⊆ D} with h𝒟
  refine ⟨⋂₀ 𝒟, convex_sInter (fun D hD => hD.1), isClosed_sInter (fun D hD => hD.2.1), ?_⟩
  ext z
  simp only [Set.mem_preimage, Set.mem_sInter]
  constructor
  · intro hz D hD
    exact hD.2.2 ⟨z, hz, rfl⟩
  · intro hall
    by_contra hz
    -- It suffices to exhibit one closed convex superset of the sweep missing `toReal z`.
    suffices h : ∃ D ∈ 𝒟, toReal z ∉ D by
      obtain ⟨D, hD, hzD⟩ := h
      exact hzD (hall D hD)
    by_cases hm : ∃ c ∈ C, det w c = det w z
    · -- Case 2: the level of `z` is attained on `C`.
      obtain ⟨c₀, hc₀, hc₀m⟩ := hm
      obtain ⟨k, hk⟩ : ∃ k : ℤ, c₀ - z = k • w := by
        refine eq_zsmul_of_det_eq_zero hw ?_
        simp only [det, Prod.fst_sub, Prod.snd_sub] at hc₀m ⊢
        linear_combination hc₀m
      have hc₀z : c₀ = z + k • w := by rw [← hk]; abel
      have hkpos : 0 < k := by
        by_contra hk0
        push Not at hk0
        apply hz
        refine ⟨c₀, hc₀, (-k).toNat, ?_⟩
        have e : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
        rw [e, hc₀z, add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]
      have hzC : z ∉ C := fun h => hz (subset_sweep C w h)
      obtain ⟨D₀, hD₀conv, hD₀closed, hCeq⟩ := hC
      have hzD₀ : toReal z ∉ D₀ := by
        intro h
        apply hzC
        rw [hCeq]
        exact h
      obtain ⟨f, u, hfD, hfz⟩ := geometric_hahn_banach_closed_point hD₀conv hD₀closed hzD₀
      have hfc₀ : f (toReal c₀) < u := hfD _ (by rw [hCeq] at hc₀; exact hc₀)
      have hsplit : f (toReal c₀) = f (toReal z) + (k : ℝ) * f (toReal w) := by
        rw [hc₀z, toReal_add, toReal_zsmul, map_add, map_smul, smul_eq_mul]
      have hfw : f (toReal w) < 0 := by
        have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
        by_contra hcon
        push Not at hcon
        have : 0 ≤ (k : ℝ) * f (toReal w) := mul_nonneg hk'.le hcon
        linarith
      refine ⟨{p | f p ≤ u}, ⟨?_, ?_, ?_⟩, ?_⟩
      · exact convex_halfSpace_le ⟨fun x y => map_add f x y, fun c x => map_smul f c x⟩ u
      · exact isClosed_le f.continuous continuous_const
      · rintro _ ⟨_, ⟨g, hg, t, rfl⟩, rfl⟩
        show f (toReal (g + (t : ℤ) • w)) ≤ u
        rw [toReal_add, toReal_zsmul, map_add, map_smul, smul_eq_mul]
        have hg' : f (toReal g) < u := hfD _ (by rw [hCeq] at hg; exact hg)
        have ht : (0 : ℝ) ≤ ((t : ℤ) : ℝ) := by exact_mod_cast Int.natCast_nonneg t
        have : ((t : ℤ) : ℝ) * f (toReal w) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hfw.le
        linarith
      · show ¬ f (toReal z) ≤ u
        push Not
        exact hfz
    · -- Case 1: the level of `z` is not attained; by `LevelInterval` all of `C` is on one side.
      push Not at hm
      have hside : (∀ c ∈ C, det w c < det w z) ∨ (∀ c ∈ C, det w z < det w c) := by
        by_contra hcon
        push Not at hcon
        obtain ⟨⟨a, ha, hza⟩, ⟨b, hb, hbz⟩⟩ := hcon
        obtain ⟨c, hc, hcm⟩ := hlev b hb a ha (det w z) hbz hza
        exact hm c hc hcm
      rcases hside with h | h
      · refine ⟨{p | rlevel w p ≤ (det w z : ℝ) - 1}, ⟨?_, ?_, ?_⟩, ?_⟩
        · exact convex_halfSpace_le (isLinearMap_rlevel w) _
        · exact isClosed_le (continuous_rlevel w) continuous_const
        · rintro _ ⟨z', hz', rfl⟩
          obtain ⟨g, hg, hlev'⟩ := rlevel_toReal_mem_sweep hz'
          show rlevel w (toReal z') ≤ (det w z : ℝ) - 1
          rw [hlev']
          have h1 : det w g ≤ det w z - 1 := by have := h g hg; omega
          have h2 : (det w g : ℝ) ≤ ((det w z - 1 : ℤ) : ℝ) := by exact_mod_cast h1
          push_cast at h2
          exact h2
        · show ¬ rlevel w (toReal z) ≤ (det w z : ℝ) - 1
          rw [rlevel_toReal]
          linarith
      · refine ⟨{p | (det w z : ℝ) + 1 ≤ rlevel w p}, ⟨?_, ?_, ?_⟩, ?_⟩
        · exact convex_halfSpace_ge (isLinearMap_rlevel w) _
        · exact isClosed_le continuous_const (continuous_rlevel w)
        · rintro _ ⟨z', hz', rfl⟩
          obtain ⟨g, hg, hlev'⟩ := rlevel_toReal_mem_sweep hz'
          show (det w z : ℝ) + 1 ≤ rlevel w (toReal z')
          rw [hlev']
          have h1 : det w z + 1 ≤ det w g := by have := h g hg; omega
          have h2 : ((det w z + 1 : ℤ) : ℝ) ≤ (det w g : ℝ) := by exact_mod_cast h1
          push_cast at h2
          exact h2
        · show ¬ (det w z : ℝ) + 1 ≤ rlevel w (toReal z)
          rw [rlevel_toReal]
          linarith

/-- **Sweep stability of `Colle41.IsRegion`.**  The rays are inherited (`rayIn_sweep_of_rayIn`);
the convexity is `isLatticeConvexRegion_sweep`.  No hypothesis relates `w` to `u` or `u'`. -/
theorem isRegion_sweep {C : Set (ℤ × ℤ)} {u u' w : ℤ × ℤ} (hR : Colle41.IsRegion C u u')
    (hw : Primitive w) (hlev : LevelInterval C w) : Colle41.IsRegion (sweep C w) u u' :=
  ⟨isLatticeConvexRegion_sweep hR.1 hw hlev,
    hR.2.1.imp fun _ h => rayIn_sweep_of_rayIn h,
    hR.2.2.imp fun _ h => rayIn_sweep_of_rayIn h⟩

/-! ## §4  Propagating `LevelInterval` along a chain

For the next sweep direction `w'`, the levels of `sweep C w` are `det w' g + t · det w' w`.
When `det w' w = ±1` these fill a half-line from any single level, so the interval condition
holds with **no** hypothesis on `C`.  When `|det w' w| ≥ 2` it can fail (§6). -/

theorem levelInterval_sweep_of_det_eq_one {C : Set (ℤ × ℤ)} {w w' : ℤ × ℤ}
    (h : det w' w = 1) : LevelInterval (sweep C w) w' := by
  rintro _ ⟨g, hg, s, rfl⟩ _ ⟨g', hg', t, rfl⟩ m hm₁ _
  have hlv : det w' (g + (s : ℤ) • w) = det w' g + (s : ℤ) := by
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h ⊢
    linear_combination (s : ℤ) * h
  rw [hlv] at hm₁
  refine ⟨g + ((m - det w' g).toNat : ℤ) • w, ⟨g, hg, _, rfl⟩, ?_⟩
  have e : (((m - det w' g).toNat : ℕ) : ℤ) = m - det w' g := Int.toNat_of_nonneg (by omega)
  rw [e]
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h ⊢
  linear_combination (m - (w'.1 * g.2 - w'.2 * g.1)) * h

theorem levelInterval_sweep_of_det_eq_neg_one {C : Set (ℤ × ℤ)} {w w' : ℤ × ℤ}
    (h : det w' w = -1) : LevelInterval (sweep C w) w' := by
  rintro _ ⟨g, hg, s, rfl⟩ _ ⟨g', hg', t, rfl⟩ m _ hm₂
  have hlv : det w' (g' + (t : ℤ) • w) = det w' g' - (t : ℤ) := by
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h ⊢
    linear_combination (t : ℤ) * h
  rw [hlv] at hm₂
  refine ⟨g' + ((det w' g' - m).toNat : ℤ) • w, ⟨g', hg', _, rfl⟩, ?_⟩
  have e : (((det w' g' - m).toNat : ℕ) : ℤ) = det w' g' - m := Int.toNat_of_nonneg (by omega)
  rw [e]
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h ⊢
  linear_combination ((w'.1 * g'.2 - w'.2 * g'.1) - m) * h

/-! ## §5  Non-vacuity: a non-degenerate positive instance

`quad` swept by `(-1, 1)`: primitive, levels `det (-1,1) z = -(z.1 + z.2)` fill `(-∞, 0]`, and
the sweep is strictly larger than `quad` (it contains `(-1, 1)`). -/

theorem isRegion_quad_right_up : Colle41.IsRegion LE2.quad (1, 0) (0, 1) :=
  ⟨LE2.isLatticeConvexRegion_quad,
    ⟨(0, 0), fun k => by
      rw [LE2.mem_quad]
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      omega⟩,
    ⟨(0, 0), fun k => by
      rw [LE2.mem_quad]
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      omega⟩⟩

theorem primitive_neg_one_one : Primitive ((-1 : ℤ), (1 : ℤ)) :=
  ⟨-1, 0, by norm_num⟩

theorem levelInterval_quad_neg_one_one : LevelInterval LE2.quad ((-1 : ℤ), (1 : ℤ)) := by
  intro a ha b hb m _ hmb
  rw [LE2.mem_quad] at hb
  refine ⟨(-m, 0), ?_, ?_⟩
  · rw [LE2.mem_quad]
    simp only [det] at hmb
    constructor <;> omega
  · simp only [det]
    ring

theorem isRegion_sweep_quad :
    Colle41.IsRegion (sweep LE2.quad ((-1 : ℤ), (1 : ℤ))) (1, 0) (0, 1) :=
  isRegion_sweep isRegion_quad_right_up primitive_neg_one_one levelInterval_quad_neg_one_one

theorem quad_ssubset_sweep : LE2.quad ⊂ sweep LE2.quad ((-1 : ℤ), (1 : ℤ)) :=
  (ssubset_sweep_iff _ _).mpr ⟨(0, 0), by rw [LE2.mem_quad]; simp, by
    rw [LE2.mem_quad]; simp⟩

/-! ## §6  Non-removability of the hypotheses (honest negatives) -/

/-- The two-point set `{(0,0), (1,2)}` is lattice-convex: it is the lattice part of the
closed segment `{p₂ = 2 p₁, 0 ≤ p₁ ≤ 1}`. -/
theorem isLatticeConvexRegion_pair :
    IsLatticeConvexRegion ({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (2 : ℤ))} : Set (ℤ × ℤ)) := by
  refine ⟨{p : ℝ × ℝ | p.2 = 2 * p.1 ∧ 0 ≤ p.1 ∧ p.1 ≤ 1}, ?_, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    obtain ⟨hx1, hx2, hx3⟩ := hx
    obtain ⟨hy1, hy2, hy3⟩ := hy
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    refine ⟨by rw [hx1, hy1]; ring, add_nonneg (mul_nonneg ha hx2) (mul_nonneg hb hy2), ?_⟩
    calc a * x.1 + b * y.1 ≤ a * 1 + b * 1 := by gcongr
      _ = 1 := by rw [mul_one, mul_one, hab]
  · exact (isClosed_eq continuous_snd (by fun_prop)).inter
      ((isClosed_le continuous_const continuous_fst).inter
        (isClosed_le continuous_fst continuous_const))
  · ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Set.mem_ofPred_eq,
      toReal]
    constructor
    · rintro (rfl | rfl) <;> norm_num
    · rintro ⟨h1, h2, h3⟩
      have h1' : z.2 = 2 * z.1 := by exact_mod_cast h1
      have h2' : 0 ≤ z.1 := by exact_mod_cast h2
      have h3' : z.1 ≤ 1 := by exact_mod_cast h3
      by_cases h0 : z.1 = 0
      · left; exact Prod.ext h0 (by rw [h1', h0]; ring)
      · right; exact Prod.ext (by omega) (by rw [h1']; omega)

theorem primitive_one_zero : Primitive ((1 : ℤ), (0 : ℤ)) :=
  ⟨1, 0, by norm_num⟩

/-- **The level condition cannot be dropped.**  `C = {(0,0),(1,2)}` is lattice-convex and
`w = (1,0)` is primitive, but the sweep contains `(0,0)` and `(2,2)` and misses `(1,1)`. -/
theorem not_isLatticeConvexRegion_sweep_pair :
    ¬ IsLatticeConvexRegion
      (sweep ({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (2 : ℤ))} : Set (ℤ × ℤ)) ((1 : ℤ), (0 : ℤ))) := by
  intro hK
  have h0 : ((0 : ℤ), (0 : ℤ)) ∈ sweep ({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (2 : ℤ))} : Set (ℤ × ℤ))
      ((1 : ℤ), (0 : ℤ)) :=
    ⟨(0, 0), by simp, 0, by simp⟩
  have h2 : ((2 : ℤ), (2 : ℤ)) ∈ sweep ({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (2 : ℤ))} : Set (ℤ × ℤ))
      ((1 : ℤ), (0 : ℤ)) :=
    ⟨(1, 2), by simp, 1, by simp⟩
  have hmid := Colle43.latticeConvexRegion_midpoint hK h0 h2
    (c := ((1 : ℤ), (1 : ℤ))) (by simp)
  obtain ⟨g, hg, t, ht⟩ := hmid
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  have ht2 := congrArg Prod.snd ht
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, mul_zero, add_zero] at ht2
  rcases hg with rfl | rfl <;> simp at ht2

/-- …and the level condition really fails there: levels `0` and `2` are attained, `1` is not. -/
theorem not_levelInterval_pair :
    ¬ LevelInterval ({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (2 : ℤ))} : Set (ℤ × ℤ)) ((1 : ℤ), (0 : ℤ)) := by
  intro h
  obtain ⟨c, hc, hcm⟩ := h (0, 0) (by simp) (1, 2) (by simp) 1 (by simp [det]) (by simp [det])
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  rcases hc with rfl | rfl <;> simp [det] at hcm

theorem isLatticeConvexRegion_singleton_zero :
    IsLatticeConvexRegion ({(0 : ℤ × ℤ)} : Set (ℤ × ℤ)) := by
  refine ⟨{((0 : ℝ), (0 : ℝ))}, convex_singleton _, isClosed_singleton, ?_⟩
  ext z
  simp only [Set.mem_singleton_iff, Set.mem_preimage, toReal, Int.cast_eq_zero,
    Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]

/-- **Primitivity cannot be dropped.**  `{0}` swept by `(2,0)` is `{(2t,0)}`, which misses `(1,0)`
between `(0,0)` and `(2,0)`; the level condition holds trivially (a single level). -/
theorem not_isLatticeConvexRegion_sweep_two :
    ¬ IsLatticeConvexRegion (sweep ({(0 : ℤ × ℤ)} : Set (ℤ × ℤ)) ((2 : ℤ), (0 : ℤ))) := by
  intro hK
  have h0 : (0 : ℤ × ℤ) ∈ sweep ({(0 : ℤ × ℤ)} : Set (ℤ × ℤ)) ((2 : ℤ), (0 : ℤ)) :=
    ⟨0, rfl, 0, by simp⟩
  have h2 : ((2 : ℤ), (0 : ℤ)) ∈ sweep ({(0 : ℤ × ℤ)} : Set (ℤ × ℤ)) ((2 : ℤ), (0 : ℤ)) :=
    ⟨0, rfl, 1, by simp⟩
  have hmid := Colle43.latticeConvexRegion_midpoint hK h0 h2
    (c := ((1 : ℤ), (0 : ℤ))) (by simp)
  obtain ⟨g, hg, t, ht⟩ := hmid
  rw [Set.mem_singleton_iff] at hg
  subst hg
  have ht1 := congrArg Prod.fst ht
  simp only [Prod.smul_fst, smul_eq_mul, zero_add] at ht1
  omega

theorem levelInterval_singleton_zero (w : ℤ × ℤ) :
    LevelInterval ({(0 : ℤ × ℤ)} : Set (ℤ × ℤ)) w := by
  intro a ha b hb m hma hmb
  rw [Set.mem_singleton_iff] at ha hb
  subst ha; subst hb
  exact ⟨0, rfl, by simp only [det, Prod.fst_zero, Prod.snd_zero] at hma hmb ⊢; omega⟩

/-- **`LevelInterval` does not propagate when `|det w' w| ≥ 2`.**  `{0}` swept by `(2,1)` has
`(0,1)`-levels `{0, -2, -4, …}`: `-1` is missed. -/
theorem not_levelInterval_sweep_two_one :
    ¬ LevelInterval (sweep ({(0 : ℤ × ℤ)} : Set (ℤ × ℤ)) ((2 : ℤ), (1 : ℤ))) ((0 : ℤ), (1 : ℤ)) := by
  intro h
  obtain ⟨c, hc, hcm⟩ := h ((2 : ℤ), (1 : ℤ)) ⟨0, rfl, 1, by simp⟩ 0 ⟨0, rfl, 0, by simp⟩ (-1)
    (by simp [det]) (by simp [det])
  obtain ⟨g, hg, t, rfl⟩ := hc
  rw [Set.mem_singleton_iff] at hg
  subst hg
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Prod.fst_zero, Prod.snd_zero] at hcm
  omega

/-- **The two-direction wedge is not lattice-convex in general.**  This is exactly the shape
`L1RegionBuild.wedgeRinf B vl u'` with `B = {0}`, `vl = (2,1)`, `u' = (0,1)`: it contains
`(0,0)` and `(2,2)` but not `(1,1)`.  So `wedgeRinf` needs `B` wide enough to fill the residues
modulo `det u' vl`, or `|det u' vl| = 1`. -/
theorem not_isLatticeConvexRegion_sweep_sweep_two_one :
    ¬ IsLatticeConvexRegion
      (sweep (sweep ({(0 : ℤ × ℤ)} : Set (ℤ × ℤ)) ((2 : ℤ), (1 : ℤ))) ((0 : ℤ), (1 : ℤ))) := by
  intro hK
  have h0 : (0 : ℤ × ℤ) ∈ sweep (sweep ({(0 : ℤ × ℤ)} : Set (ℤ × ℤ)) ((2 : ℤ), (1 : ℤ)))
      ((0 : ℤ), (1 : ℤ)) :=
    ⟨0, ⟨0, rfl, 0, by simp⟩, 0, by simp⟩
  have h2 : ((2 : ℤ), (2 : ℤ)) ∈ sweep (sweep ({(0 : ℤ × ℤ)} : Set (ℤ × ℤ)) ((2 : ℤ), (1 : ℤ)))
      ((0 : ℤ), (1 : ℤ)) :=
    ⟨(2, 1), ⟨0, rfl, 1, by simp⟩, 1, by simp⟩
  have hmid := Colle43.latticeConvexRegion_midpoint hK h0 h2
    (c := ((1 : ℤ), (1 : ℤ))) (by simp)
  obtain ⟨_, ⟨g, hg, s, rfl⟩, t, ht⟩ := hmid
  rw [Set.mem_singleton_iff] at hg
  subst hg
  have ht1 := congrArg Prod.fst ht
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, zero_add, mul_zero,
    add_zero] at ht1
  omega

#print axioms sweep_sweep_self
#print axioms sweep_sweep_comm
#print axioms ssubset_sweep_iff
#print axioms sweep_eq_self_iff
#print axioms rayIn_sweep_of_rayIn
#print axioms isLatticeConvexRegion_sweep
#print axioms isRegion_sweep
#print axioms levelInterval_sweep_of_det_eq_one
#print axioms levelInterval_sweep_of_det_eq_neg_one
#print axioms isRegion_sweep_quad
#print axioms quad_ssubset_sweep
#print axioms isLatticeConvexRegion_pair
#print axioms not_isLatticeConvexRegion_sweep_pair
#print axioms not_levelInterval_pair
#print axioms not_isLatticeConvexRegion_sweep_two
#print axioms levelInterval_singleton_zero
#print axioms not_levelInterval_sweep_two_one
#print axioms not_isLatticeConvexRegion_sweep_sweep_two_one

end Nivat.RegionSweep
