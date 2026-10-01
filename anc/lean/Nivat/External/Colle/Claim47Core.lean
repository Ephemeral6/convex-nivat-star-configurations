/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Defs.Config
import Nivat.Defs.Complexity
import Nivat.Defs.Orbit
import Nivat.Lattice.Primitive
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.ShellGeom
import Nivat.External.Colle.KariMoutot
import Nivat.External.Colle.R2Orientation
import Nivat.External.Colle.Generating
import Nivat.External.Colle.Lemma41
import Nivat.External.Colle.OrbitClosureBasics

/-!
# Claim 4.7 (`b3_colle2.txt:822-852`) — the pieces

Everything `Nivat.ColleReg.case1_claim47_semiAmbiguous` (`RegionSteps.lean`) needs, in
dependency order.  Collé's proof is three moves and this file has one section per move:

1. **the edge** (`Nivat.ColleReg`, below) — `Q = S \ ℓ'_S` is cut out by a *real* normal in the
   statement of L2; `edge_integral_normal` replaces it by an integral one, and
   `exists_face_end_data_gen` picks the `+u'`-end `g` of that edge together with the
   lattice-convexity of `S.erase g` that `IsGeneratingSet` demands.
2. **betweenness** (`Nivat.Claim47`) — `latticeConvex_between`: the edge points behind `g` are
   an unbroken run `g - j•u'`, `0 ≤ j ≤ k`.  This is what stops the induction of move 3 from
   falling through a hole.
3. **the induction** (`Nivat.Claim47`) — `window_period_of_not_ambiguous` (Collé's `(4.5)`,
   `:836`) and `ray_period_of_window_period` (the `η`-generating induction of `:844`).

Assembled from `tmp/L2_faceend_fwd.lean`, `tmp/L2_between.lean`, `tmp/L2_edge_normal.lean`,
`tmp/L2_core.lean`, each of which was kernel-checked standalone before landing.
-/

set_option autoImplicit false

namespace Nivat.ColleReg

open Nivat Nivat.LE2

open Nivat Nivat.LE2

/-- The primitive normal `(-v.2, v.1)` of `v` (copied from `tmp/L1_claim46.lean:1006`). -/
def perp (v : ℤ × ℤ) : ℤ × ℤ := (-v.2, v.1)

theorem dot_perp (v w : ℤ × ℤ) : Nivat.LE2.dot (perp v) w = det v w := by
  simp only [Nivat.LE2.dot, perp, det]; ring

theorem dot_zsmul_right (n : ℤ × ℤ) (k : ℤ) (v : ℤ × ℤ) :
    Nivat.LE2.dot n (k • v) = k * Nivat.LE2.dot n v := by
  simp only [Nivat.LE2.dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem sq_add_sq_pos_of_ne_zero {e : ℤ × ℤ} (he : e ≠ 0) : 0 < e.1 ^ 2 + e.2 ^ 2 := by
  by_contra h
  push_neg at h
  apply he
  have h1 : e.1 = 0 := by nlinarith [sq_nonneg e.1, sq_nonneg e.2]
  have h2 : e.2 = 0 := by nlinarith [sq_nonneg e.1, sq_nonneg e.2]
  exact Prod.ext h1 h2

theorem dot_self_pos {v : ℤ × ℤ} (hv : v ≠ 0) : 0 < Nivat.LE2.dot v v := by
  have := sq_add_sq_pos_of_ne_zero hv
  simp only [Nivat.LE2.dot]; nlinarith

/-- `perp` preserves primitivity (copied from `tmp/L1_claim46.lean:2111`). -/
theorem primitive_perp {v : ℤ × ℤ} (hv : Primitive v) : Primitive (perp v) := by
  unfold Primitive at hv ⊢
  show IsCoprime (-v.2) v.1
  exact hv.symm.neg_left

/-- The `+u'`-end `a` of the `perp u'`-face of a finite nonempty `B`: it still maximises
`perp u'` (same face as `exists_face_end`), but now every other face point is `a - k•u'`,
`k ≥ 0` — the mirror image of `exists_face_end` (`tmp/L1_claim46.lean:2079`). -/
theorem exists_face_end_fwd {B : Finset (ℤ × ℤ)} (hB : B.Nonempty) {u' : ℤ × ℤ}
    (hu' : Primitive u') :
    ∃ a ∈ B, (∀ b ∈ B, Nivat.LE2.dot (perp u') b ≤ Nivat.LE2.dot (perp u') a) ∧
      ∀ b ∈ B, Nivat.LE2.dot (perp u') b = Nivat.LE2.dot (perp u') a →
        ∃ k : ℕ, b = a - (k : ℤ) • u' := by
  classical
  obtain ⟨m, hmB, hmmax⟩ := B.exists_max_image (Nivat.LE2.dot (perp u')) hB
  set F : Finset (ℤ × ℤ) :=
    B.filter (fun b => Nivat.LE2.dot (perp u') b = Nivat.LE2.dot (perp u') m) with hF
  obtain ⟨a, haF, hamax⟩ := F.exists_max_image (Nivat.LE2.dot u')
    ⟨m, Finset.mem_filter.mpr ⟨hmB, rfl⟩⟩
  have haB : a ∈ B := (Finset.mem_filter.mp haF).1
  have halev : Nivat.LE2.dot (perp u') a = Nivat.LE2.dot (perp u') m :=
    (Finset.mem_filter.mp haF).2
  refine ⟨a, haB, fun b hb => halev ▸ hmmax b hb, fun b hb hlev => ?_⟩
  have hbF : b ∈ F := Finset.mem_filter.mpr ⟨hb, hlev.trans halev⟩
  have hdet : det u' (b - a) = 0 := by
    rw [← dot_perp, Nivat.LE2.dot_sub, hlev, sub_self]
  obtain ⟨c, hc⟩ := eq_zsmul_of_det_eq_zero hu' hdet
  have hc0 : c ≤ 0 := by
    have h1 := hamax b hbF
    have h2 : Nivat.LE2.dot u' b - Nivat.LE2.dot u' a = c * Nivat.LE2.dot u' u' := by
      rw [← Nivat.LE2.dot_sub, hc, dot_zsmul_right]
    have hpos := dot_self_pos hu'.ne_zero
    by_contra hpos'
    push_neg at hpos'
    nlinarith
  refine ⟨(-c).toNat, ?_⟩
  have hcnt : ((-c).toNat : ℤ) = -c := Int.toNat_of_nonneg (by omega)
  have hba : b = a + c • u' := by rw [← hc]; abel
  rw [hcnt, neg_smul, sub_neg_eq_add]
  exact hba

/-! ### Decoupled version: an arbitrary normal `n ≠ 0` orthogonal to the primitive `d`

`case1_claim47_semiAmbiguous`'s edge normal `n` is only known up to sign relative to
`perp u'` (`RegionSteps.lean:965-970`), and independently the sweep always needs the
*forward* end along `d`.  The `±u'` trick above couples "which face" to "which end" the
wrong way (see the file docstring), so here `n` and `d` are decoupled into separate
parameters; the only load-bearing use of `perp` in the proof of `exists_face_end_fwd`
above was to turn `det u' (b - a) = 0` into a `dot`-orthogonality fact, and that step
generalises verbatim via `Nivat.LE2.det_eq_zero_of_dot_eq_zero` (the same move
`FaceData.lean:229`, `:255` make with `hnJ : n ≠ 0`, `hdotnJvJ : dot n v = 0`). -/

/-- The `dot d`-maximal point `a` of the `dot n`-maximal face of a finite nonempty `B`,
for any `n ≠ 0` and any primitive `d` with `dot n d = 0`: every other face point is
`a - k•d`, `k ≥ 0`.  Generalises `exists_face_end_fwd` (`n := perp u'`, `d := u'`). -/
theorem exists_face_end_fwd_gen {B : Finset (ℤ × ℤ)} (hB : B.Nonempty) {n d : ℤ × ℤ}
    (hd : Primitive d) (hn : n ≠ 0) (hnd : Nivat.LE2.dot n d = 0) :
    ∃ a ∈ B, (∀ b ∈ B, Nivat.LE2.dot n b ≤ Nivat.LE2.dot n a) ∧
      ∀ b ∈ B, Nivat.LE2.dot n b = Nivat.LE2.dot n a →
        ∃ k : ℕ, b = a - (k : ℤ) • d := by
  classical
  obtain ⟨m, hmB, hmmax⟩ := B.exists_max_image (Nivat.LE2.dot n) hB
  set F : Finset (ℤ × ℤ) :=
    B.filter (fun b => Nivat.LE2.dot n b = Nivat.LE2.dot n m) with hF
  obtain ⟨a, haF, hamax⟩ := F.exists_max_image (Nivat.LE2.dot d)
    ⟨m, Finset.mem_filter.mpr ⟨hmB, rfl⟩⟩
  have haB : a ∈ B := (Finset.mem_filter.mp haF).1
  have halev : Nivat.LE2.dot n a = Nivat.LE2.dot n m :=
    (Finset.mem_filter.mp haF).2
  refine ⟨a, haB, fun b hb => halev ▸ hmmax b hb, fun b hb hlev => ?_⟩
  have hbF : b ∈ F := Finset.mem_filter.mpr ⟨hb, hlev.trans halev⟩
  have hdet : det d (b - a) = 0 :=
    Nivat.LE2.det_eq_zero_of_dot_eq_zero hn hnd
      (by rw [Nivat.LE2.dot_sub, hlev, sub_self])
  obtain ⟨c, hc⟩ := eq_zsmul_of_det_eq_zero hd hdet
  have hc0 : c ≤ 0 := by
    have h1 := hamax b hbF
    have h2 : Nivat.LE2.dot d b - Nivat.LE2.dot d a = c * Nivat.LE2.dot d d := by
      rw [← Nivat.LE2.dot_sub, hc, dot_zsmul_right]
    have hpos := dot_self_pos hd.ne_zero
    by_contra hpos'
    push_neg at hpos'
    nlinarith
  refine ⟨(-c).toNat, ?_⟩
  have hcnt : ((-c).toNat : ℤ) = -c := Int.toNat_of_nonneg (by omega)
  have hba : b = a + c • d := by rw [← hc]; abel
  rw [hcnt, neg_smul, sub_neg_eq_add]
  exact hba

/-- The `dot d`-forward end of a `dot n`-face of a lattice-convex `S`, with the
lattice-convexity of the erasure.  Generalises `exists_face_end_data_fwd`
(`n := perp u'`, `d := u'`). -/
theorem exists_face_end_data_gen {S : Finset (ℤ × ℤ)} (hne : S.Nonempty)
    (hconv : Nivat.LatticeConvex S) {n d : ℤ × ℤ}
    (hd : Primitive d) (hn : n ≠ 0) (hnd : Nivat.LE2.dot n d = 0) :
    ∃ a ∈ S, Nivat.LatticeConvex (S.erase a) ∧
      (∀ b ∈ S, Nivat.LE2.dot n b ≤ Nivat.LE2.dot n a) ∧
      (∀ b ∈ S, Nivat.LE2.dot n b = Nivat.LE2.dot n a →
        ∃ k : ℕ, b = a - (k : ℤ) • d) := by
  classical
  obtain ⟨a, ha, htop, hface⟩ := exists_face_end_fwd_gen hne hd hn hnd
  refine ⟨a, ha, ?_, htop, hface⟩
  refine Nivat.Colle37Geom.latticeConvex_erase_of_lexExtreme hconv (n := n) (d := d) ?_
  intro b hb
  have hbS := Finset.mem_of_mem_erase hb
  have hba := Finset.ne_of_mem_erase hb
  rcases lt_or_eq_of_le (htop b hbS) with h | h
  · exact Or.inl h
  · right
    refine ⟨h, ?_⟩
    obtain ⟨k, hk⟩ := hface b hbS h
    have hk1 : (1 : ℤ) ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · exfalso; apply hba; rw [hk, h0]; simp
      · exact_mod_cast h0
    rw [hk, Nivat.LE2.dot_sub, dot_zsmul_right]
    have := dot_self_pos hd.ne_zero
    nlinarith

/-- `n := perp u'`, `d := u'` instance of `exists_face_end_data_gen`: the top `perp u'`-face,
forward end along `u'`. -/
theorem exists_face_end_data_perp {S : Finset (ℤ × ℤ)} (hne : S.Nonempty)
    (hconv : Nivat.LatticeConvex S) {u' : ℤ × ℤ} (hu' : Primitive u') :
    ∃ a ∈ S, Nivat.LatticeConvex (S.erase a) ∧
      (∀ b ∈ S, Nivat.LE2.dot (perp u') b ≤ Nivat.LE2.dot (perp u') a) ∧
      (∀ b ∈ S, Nivat.LE2.dot (perp u') b = Nivat.LE2.dot (perp u') a →
        ∃ k : ℕ, b = a - (k : ℤ) • u') :=
  exists_face_end_data_gen hne hconv hu' (primitive_perp hu').ne_zero
    (by rw [dot_perp]; simp only [det]; ring)

/-- `n := -perp u'`, `d := u'` instance of `exists_face_end_data_gen`: the *bottom* `perp u'`-
face (i.e. the top `-perp u'`-face), forward end along `u'` — the combination the `±u'`
negation trick could not reach (see the file docstring). -/
theorem exists_face_end_data_perp_neg {S : Finset (ℤ × ℤ)} (hne : S.Nonempty)
    (hconv : Nivat.LatticeConvex S) {u' : ℤ × ℤ} (hu' : Primitive u') :
    ∃ a ∈ S, Nivat.LatticeConvex (S.erase a) ∧
      (∀ b ∈ S, Nivat.LE2.dot (-perp u') b ≤ Nivat.LE2.dot (-perp u') a) ∧
      (∀ b ∈ S, Nivat.LE2.dot (-perp u') b = Nivat.LE2.dot (-perp u') a →
        ∃ k : ℕ, b = a - (k : ℤ) • u') :=
  exists_face_end_data_gen hne hconv hu' (neg_ne_zero.mpr (primitive_perp hu').ne_zero)
    (by rw [Nivat.LE2.dot_neg_left, dot_perp]; simp only [det]; ring)

/-- The `+u'`-end of a lattice-convex face, with the lattice-convexity of the erasure — the
mirror image of `exists_face_end_data` (`tmp/L1_claim46.lean:2200`).  Kept as the original
statement (now a one-line corollary of `exists_face_end_data_perp`) so nothing that already
typechecked is lost. -/
theorem exists_face_end_data_fwd {S : Finset (ℤ × ℤ)} (hne : S.Nonempty)
    (hconv : Nivat.LatticeConvex S) {u' : ℤ × ℤ} (hu' : Primitive u') :
    ∃ a ∈ S, Nivat.LatticeConvex (S.erase a) ∧
      (∀ b ∈ S, Nivat.LE2.dot (perp u') b ≤ Nivat.LE2.dot (perp u') a) ∧
      (∀ b ∈ S, Nivat.LE2.dot (perp u') b = Nivat.LE2.dot (perp u') a →
        ∃ k : ℕ, b = a - (k : ℤ) • u') :=
  exists_face_end_data_perp hne hconv hu'

end Nivat.ColleReg

namespace Nivat.Claim47

open Nivat Nivat.Colle41

variable {A : Type*}

open Nivat

/-- **G3.**  Along a fixed lattice direction `u`, a lattice-convex `Finset` contains every
lattice point between two of its points.

This is `Nivat.Colle43.between_mem` (`Claim43.lean:229`) transposed from
`IsLatticeConvexRegion` on a `Set` to `LatticeConvex` on a `Finset`; the arithmetic is that
proof's, with `C := Conv S`.

假设消费预表 (签名落地协议 step 2):
* `hS`   — the very last step, `hS _ : toReal _ ∈ Conv S → _ ∈ S`.
* `ha`   — twice: as the left endpoint of the convex combination (via `subset_Conv`), and in
           the degenerate branch `a = b`, where it *is* the conclusion.
* `hb`   — as the right endpoint of the convex combination.
* `hm1`  — for `0 ≤ t`, and (with `hm2`) to split on `a = b` versus `a < b`.
* `hm2`  — for `t ≤ 1`, hence for `0 ≤ 1 - t`.

No hypothesis is idle, and none is missing: in particular `u = 0` is allowed (the
combination degenerates to `z₀`, which `ha` already places in `S`). -/
theorem latticeConvex_between {S : Finset (ℤ × ℤ)} (hS : Nivat.LatticeConvex S)
    {z₀ u : ℤ × ℤ} {a b m : ℤ}
    (ha : z₀ + a • u ∈ S) (hb : z₀ + b • u ∈ S) (hm1 : a ≤ m) (hm2 : m ≤ b) :
    z₀ + m • u ∈ S := by
  apply hS
  rcases eq_or_lt_of_le (hm1.trans hm2) with hab | hab
  · -- `a = b`, so `m = a` and there is nothing to interpolate.
    have hma : m = a := by omega
    rw [hma]
    exact subset_Conv ha
  · set t : ℝ := ((m : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)) with ht
    have hba : (0 : ℝ) < (b : ℝ) - (a : ℝ) := by
      have : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
      linarith
    have ht0 : 0 ≤ t := by
      apply div_nonneg _ (le_of_lt hba)
      have : (a : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      linarith
    have ht1 : t ≤ 1 := by
      rw [ht, div_le_one hba]
      have : (m : ℝ) ≤ (b : ℝ) := by exact_mod_cast hm2
      linarith
    have key : toReal (z₀ + m • u) =
        (1 - t) • toReal (z₀ + a • u) + t • toReal (z₀ + b • u) := by
      have hne : ((b : ℝ) - (a : ℝ)) ≠ 0 := ne_of_gt hba
      apply Prod.ext <;>
        simp only [toReal, Prod.fst_add, Prod.snd_add, Prod.smul_def, smul_eq_mul,
          Prod.mk_add_mk] <;>
        push_cast <;>
        rw [ht] <;> field_simp <;> ring
    rw [key, Conv]
    exact (convex_convexHull ℝ _) (subset_Conv ha) (subset_Conv hb) (by linarith) ht0 (by ring)

/-- The specialisation L2 calls: the backward run `g, g - u, …, g - k•u` is unbroken.

⚠ `hg : g ∈ S` is **not** removable.  Betweenness needs two endpoints, and `hk` supplies only
the far one; with `hg` dropped the statement is false — take `u ≠ 0`, `S := {g - k•u}` (a
singleton, hence lattice-convex) and any `j < k`, so that `g - j•u ∉ S`.  This matters because
`ray_period_of_window_period`'s `hSseg` (`tmp/L2_core.lean:141`) is stated *without* it:

    (hSseg : ∀ j k : ℕ, j ≤ k → g - (k : ℤ) • u' ∈ S → g - (j : ℤ) • u' ∈ S)

To close that hypothesis from this lemma, feed `g ∈ S` from `hgen.1`
(`Nivat.Colle.GeneratesAt`'s first conjunct, `Generating.lean:19`), which that theorem
already has in scope as `hgen : GeneratesAt ξ S g`. -/
theorem latticeConvex_between_sub {S : Finset (ℤ × ℤ)} (hS : Nivat.LatticeConvex S)
    {g u : ℤ × ℤ} {k j : ℕ} (hg : g ∈ S) (hk : g - (k : ℤ) • u ∈ S) (hjk : j ≤ k) :
    g - (j : ℤ) • u ∈ S := by
  have e : ∀ n : ℤ, g + (-n) • u = g - n • u := by
    intro n; rw [neg_smul]; abel
  have ha : g + (-(k : ℤ)) • u ∈ S := by rw [e]; exact hk
  have hb : g + (0 : ℤ) • u ∈ S := by simpa using hg
  have h := latticeConvex_between (m := -(j : ℤ)) hS ha hb (by omega) (by omega)
  rw [e] at h
  exact h

/-- Sanity check that the specialisation really is the `hSseg` shape, `g ∈ S` aside. -/
theorem hSseg_of_latticeConvex {S : Finset (ℤ × ℤ)} (hS : Nivat.LatticeConvex S)
    {g u' : ℤ × ℤ} (hg : g ∈ S) :
    ∀ j k : ℕ, j ≤ k → g - (k : ℤ) • u' ∈ S → g - (j : ℤ) • u' ∈ S :=
  fun _ _ hjk hk => latticeConvex_between_sub hS hg hk hjk

open Nivat

/-! ### Cancelling a non-zero real factor, in both signs -/

private theorem mul_le_iff_of_pos {t a b : ℝ} (ht : 0 < t) : t * a ≤ t * b ↔ a ≤ b :=
  ⟨fun h => by nlinarith, fun h => by nlinarith⟩

private theorem mul_lt_iff_of_pos {t a b : ℝ} (ht : 0 < t) : t * a < t * b ↔ a < b :=
  ⟨fun h => by nlinarith, fun h => by nlinarith⟩

private theorem mul_le_iff_of_neg {t a b : ℝ} (ht : t < 0) : t * a ≤ t * b ↔ b ≤ a :=
  ⟨fun h => by nlinarith, fun h => by nlinarith⟩

private theorem mul_lt_iff_of_neg {t a b : ℝ} (ht : t < 0) : t * a < t * b ↔ b < a :=
  ⟨fun h => by nlinarith, fun h => by nlinarith⟩

/-! ### The bridge -/

/-- **The edge cut out by a real normal is cut out by an integral one.**

Given `n : ℝ × ℝ` non-zero and orthogonal to `u'`, bounded above on `S` by `cmax` with the
level `cmax` attained, there is an integral `nI` orthogonal to `u'` and a point `g₀ ∈ S` at
which `dot nI ·` is maximal on `S`, such that `Q` is exactly the part of `S` strictly below
`g₀`'s level.

`nI` is `Nivat.KM.perpOf u' = (-u'.2, u'.1)` up to sign; the sign is genuinely not determined
by the hypotheses, since `n` and `-n` both satisfy `inner2 · u' = 0`. -/
theorem edge_integral_normal {S Q : Finset (ℤ × ℤ)} {u' : ℤ × ℤ} (hu' : u' ≠ 0)
    {n : ℝ × ℝ} {cmax : ℝ} (hn : n ≠ 0) (hnu : inner2 n u' = 0)
    (hle : ∀ z ∈ S, inner2 n z ≤ cmax)
    (hface : (Nivat.R2.face S n cmax).Nonempty)
    (hQ : Q = S.filter fun z => inner2 n z < cmax) :
    ∃ nI : ℤ × ℤ, nI ≠ 0 ∧ Nivat.LE2.dot nI u' = 0 ∧
      ∃ g₀ ∈ S, (∀ z ∈ S, Nivat.LE2.dot nI z ≤ Nivat.LE2.dot nI g₀) ∧
        ∀ z ∈ S, (z ∈ Q ↔ Nivat.LE2.dot nI z < Nivat.LE2.dot nI g₀) := by
  classical
  -- `n` lies on the real line spanned by `perpOf u'`.
  obtain ⟨t, ht⟩ := Nivat.KM.exists_smul_perpOf hu' hnu
  have hp0 : Nivat.KM.perpOf u' ≠ 0 := Nivat.KM.perpOf_ne_zero hu'
  have hpu : Nivat.LE2.dot (Nivat.KM.perpOf u') u' = 0 := by
    simp only [Nivat.LE2.dot, Nivat.KM.perpOf]
    ring
  set p : ℤ × ℤ := Nivat.KM.perpOf u' with hpdef
  -- The multiplier is non-zero, else `n = 0`.
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hn (by rw [ht]; simp)
  -- On lattice points, `inner2 n` *is* `t • dot p`.
  have hval : ∀ z : ℤ × ℤ, inner2 n z = t * ((Nivat.LE2.dot p z : ℤ) : ℝ) := by
    intro z
    rw [ht, Nivat.KM.inner2_smul_left, Nivat.LE2.inner2_toReal]
  -- A face point attains `cmax`.
  obtain ⟨g₀, hg₀⟩ := hface
  obtain ⟨hg₀S, hg₀c⟩ := Nivat.R2.mem_face.mp hg₀
  rcases lt_or_gt_of_ne ht0 with htneg | htpos
  · -- `t < 0`: the order is reversed, so the integral normal is `-p`.
    refine ⟨-p, neg_ne_zero.mpr hp0, ?_, g₀, hg₀S, ?_, ?_⟩
    · rw [Nivat.LE2.dot_neg_left, hpu, neg_zero]
    · intro z hz
      have h1 : t * ((Nivat.LE2.dot p z : ℤ) : ℝ) ≤ t * ((Nivat.LE2.dot p g₀ : ℤ) : ℝ) := by
        rw [← hval z, ← hval g₀, hg₀c]
        exact hle z hz
      have h2 : Nivat.LE2.dot p g₀ ≤ Nivat.LE2.dot p z := by
        exact_mod_cast (mul_le_iff_of_neg htneg).mp h1
      simp only [Nivat.LE2.dot_neg_left]
      omega
    · intro z hz
      rw [hQ, Finset.mem_filter]
      simp only [Nivat.LE2.dot_neg_left]
      constructor
      · rintro ⟨-, hlt⟩
        have h1 : t * ((Nivat.LE2.dot p z : ℤ) : ℝ) < t * ((Nivat.LE2.dot p g₀ : ℤ) : ℝ) := by
          rw [← hval z, ← hval g₀, hg₀c]
          exact hlt
        have h2 : Nivat.LE2.dot p g₀ < Nivat.LE2.dot p z := by
          exact_mod_cast (mul_lt_iff_of_neg htneg).mp h1
        omega
      · intro hlt
        refine ⟨hz, ?_⟩
        have h2 : Nivat.LE2.dot p g₀ < Nivat.LE2.dot p z := by omega
        have h3 : ((Nivat.LE2.dot p g₀ : ℤ) : ℝ) < ((Nivat.LE2.dot p z : ℤ) : ℝ) := by
          exact_mod_cast h2
        have h4 := (mul_lt_iff_of_neg htneg).mpr h3
        rw [← hval z, ← hval g₀, hg₀c] at h4
        exact h4
  · -- `t > 0`: the order is preserved, so the integral normal is `p` itself.
    refine ⟨p, hp0, hpu, g₀, hg₀S, ?_, ?_⟩
    · intro z hz
      have h1 : t * ((Nivat.LE2.dot p z : ℤ) : ℝ) ≤ t * ((Nivat.LE2.dot p g₀ : ℤ) : ℝ) := by
        rw [← hval z, ← hval g₀, hg₀c]
        exact hle z hz
      exact_mod_cast (mul_le_iff_of_pos htpos).mp h1
    · intro z hz
      rw [hQ, Finset.mem_filter]
      constructor
      · rintro ⟨-, hlt⟩
        have h1 : t * ((Nivat.LE2.dot p z : ℤ) : ℝ) < t * ((Nivat.LE2.dot p g₀ : ℤ) : ℝ) := by
          rw [← hval z, ← hval g₀, hg₀c]
          exact hlt
        exact_mod_cast (mul_lt_iff_of_pos htpos).mp h1
      · intro hlt
        refine ⟨hz, ?_⟩
        have h3 : ((Nivat.LE2.dot p z : ℤ) : ℝ) < ((Nivat.LE2.dot p g₀ : ℤ) : ℝ) := by
          exact_mod_cast hlt
        have h4 := (mul_lt_iff_of_pos htpos).mpr h3
        rw [← hval z, ← hval g₀, hg₀c] at h4
        exact h4

open Nivat Nivat.Colle41

variable {A : Type*}

/-- **Step B.**  At a single `t₀ ≥ τ` at which semi-ambiguity fails, the *whole* `S`-window of
`ξ'` at `t₀ • u'` is `c•u`-periodic.

This is Collé's `(4.5)` (`b3_colle2.txt:836`) at one position.  `hfail` is exactly the
`push_neg` of `SemiAmbiguousAlong`'s body at `t₀`, i.e. his `N_𝒯(ℓ', γ) = 1`.

假设消费预表 (签名落地协议 step 2), every hypothesis, where it is eaten:
* `hξ'`  — twice, to produce the two `S`-windows `a` and `b` of `ξ` that `hfail` compares.
* `hQS`  — to feed `hfail`'s two premises, which range over `Q`, from the windows `hA`/`hB`,
           which are produced over `S`.
* `hRper`, `hQR` — together, to move `ξ'` across `c•u` on the `Q`-part, which is what makes
           `b` satisfy `hfail`'s second premise.
* `ht₀`  — feeding `hQR`.
-/
theorem window_period_of_not_ambiguous
    {ξ ξ' : Config A} (hξ' : ξ' ∈ orbitClosure ξ)
    {S Q : Finset (ℤ × ℤ)} (hQS : Q ⊆ S)
    {u u' : ℤ × ℤ} {c : ℤ} {R : Set (ℤ × ℤ)} {τ t₀ : ℤ}
    (hRper : PeriodOn ξ' R (c • u))
    (hQR : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R)
    (ht₀ : τ ≤ t₀)
    (hfail : ∀ a b : ℤ × ℤ,
      (∀ z ∈ Q, ξ (a + z) = ξ' (t₀ • u' + z)) →
      (∀ z ∈ Q, ξ (b + z) = ξ' (t₀ • u' + z)) →
      ∀ z ∈ S, ξ (a + z) = ξ (b + z)) :
    ∀ z ∈ S, ξ' (t₀ • u' + z + c • u) = ξ' (t₀ • u' + z) := by
  classical
  -- The `S`-window of `ξ'` at `t₀ • u'`, pulled back to a window of `ξ` at `a`.
  obtain ⟨w₁, hw₁⟩ := hξ' (S.image fun z => t₀ • u' + z)
  set a : ℤ × ℤ := w₁ + t₀ • u' with ha
  have hA : ∀ z ∈ S, ξ (a + z) = ξ' (t₀ • u' + z) := by
    intro z hz
    have h := hw₁ (t₀ • u' + z) (Finset.mem_image_of_mem _ hz)
    have e : w₁ + (t₀ • u' + z) = a + z := by rw [ha]; abel
    rw [h, e]
  -- The `S`-window of `ξ'` at `t₀ • u' + c • u`, pulled back to a window of `ξ` at `b`.
  obtain ⟨w₂, hw₂⟩ := hξ' (S.image fun z => t₀ • u' + z + c • u)
  set b : ℤ × ℤ := w₂ + (t₀ • u' + c • u) with hb
  have hB : ∀ z ∈ S, ξ (b + z) = ξ' (t₀ • u' + z + c • u) := by
    intro z hz
    have h := hw₂ (t₀ • u' + z + c • u) (Finset.mem_image_of_mem _ hz)
    have e : w₂ + (t₀ • u' + z + c • u) = b + z := by rw [hb]; abel
    rw [h, e]
  -- On `Q` the two windows agree, because `c • u` is a period of `ξ'` on `R ⊇ Q`-positions.
  have hQper : ∀ z ∈ Q, ξ' (t₀ • u' + z + c • u) = ξ' (t₀ • u' + z) := by
    intro z hz
    obtain ⟨hmem, hmem'⟩ := hQR t₀ ht₀ z hz
    exact hRper (t₀ • u' + z) hmem hmem'
  -- `hfail` now applies to `a` and `b`, and its conclusion on `S` is the claim.
  intro z hz
  have hfa : ∀ y ∈ Q, ξ (a + y) = ξ' (t₀ • u' + y) := fun y hy => hA y (hQS hy)
  have hfb : ∀ y ∈ Q, ξ (b + y) = ξ' (t₀ • u' + y) :=
    fun y hy => (hB y (hQS hy)).trans (hQper y hy)
  have hkey := hfail a b hfa hfb z hz
  rw [hA z hz, hB z hz] at hkey
  exact hkey.symm

/-! ## Step C — the generating-set induction along the `ℓ'`-ray

Collé `b3_colle2.txt:844`: *"(4.5) and the fact that `𝒯` is `η`-generating allow us to obtain
by induction that ... for `t ≥ t₀`"*.  Figure 11(A). -/

/-- `GeneratesAt` is stated at the origin (`Generating.lean:17-20`); this is the same statement
with the window placed at `w`.  The move is `T`-conjugation plus
`Colle.mem_orbitClosure_trans` (`OrbitClosureBasics.lean:19`). -/
theorem generatesAt_translate {ξ : Config A} {S : Finset (ℤ × ℤ)} {g : ℤ × ℤ}
    (hgen : Nivat.Colle.GeneratesAt ξ S g) {x y : Config A}
    (hx : x ∈ orbitClosure ξ) (hy : y ∈ orbitClosure ξ) (w : ℤ × ℤ)
    (h : ∀ z ∈ S.erase g, x (w + z) = y (w + z)) : x (w + g) = y (w + g) := by
  have hx' : T w x ∈ orbitClosure ξ :=
    Nivat.Colle.mem_orbitClosure_trans hx (T_mem_orbitClosure x w)
  have hy' : T w y ∈ orbitClosure ξ :=
    Nivat.Colle.mem_orbitClosure_trans hy (T_mem_orbitClosure y w)
  have hagr : ∀ z ∈ S.erase g, T w x z = T w y z := by
    intro z hz
    simp only [T, add_comm z w]
    exact h z hz
  have := hgen.2 (T w x) hx' (T w y) hy' hagr
  simpa only [T, add_comm g w] using this

private theorem shift_sub_smul (s k : ℤ) (g v : ℤ × ℤ) :
    s • v + (g - k • v) = (s - k) • v + g := by
  rw [sub_smul]; abel

/-- **Step C.**  From the single-position periodicity of Step B, the `c•u`-periodicity of `ξ'`
propagates along the whole forward `u'`-ray through `g`.

`g` is the **forward end** of the edge `S \ Q`: `hedge` says every other edge point sits at
`g - k•u'`, `k ≥ 1`, i.e. *behind* `g`.  That orientation is what makes the induction run —
placing the window at parameter `t` puts its edge points at parameters `t - k < t`, which are
already known.  The backward end would put them at `t + k` and the induction would not close.

假设消费预表:
* `hgen` — the induction step, once per `t`, through `generatesAt_translate`.
* `hedge` — to classify a window point off `Q` as a ray point at an earlier parameter.
* `hSseg` — the bottom of the induction: when `k` overshoots `m`, the needed ray parameter
  `t₀ - (k - m)` is supplied by `hbase` at the intermediate edge point `g - (k-m)•u'`, which
  lies in `S` only because `S` is lattice-convex.  Discharged by the `latticeConvex_between`
  lane; carried as a hypothesis here so this file stays `sorry`-free.
* `hRper`, `hQR`, `ht₀` — the `Q`-part of every window, at every parameter `≥ τ`.
* `hbase` — Step B's output; supplies both `m = 0` and every below-`t₀` parameter.
* `hξ'` — to place `ξ'` and its `c•u`-translate in `orbitClosure ξ`.
-/
theorem ray_period_of_window_period
    {ξ ξ' : Config A} (hξ' : ξ' ∈ orbitClosure ξ)
    {S Q : Finset (ℤ × ℤ)} {u u' g : ℤ × ℤ} {c : ℤ} {R : Set (ℤ × ℤ)} {τ t₀ : ℤ}
    (hgen : Nivat.Colle.GeneratesAt ξ S g)
    (hedge : ∀ z ∈ S, z ∉ Q → ∃ k : ℕ, z = g - (k : ℤ) • u')
    (hSseg : ∀ j k : ℕ, j ≤ k → g - (k : ℤ) • u' ∈ S → g - (j : ℤ) • u' ∈ S)
    (hRper : PeriodOn ξ' R (c • u))
    (hQR : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R)
    (ht₀ : τ ≤ t₀)
    (hbase : ∀ z ∈ S, ξ' (t₀ • u' + z + c • u) = ξ' (t₀ • u' + z)) :
    ∀ t : ℤ, t₀ ≤ t → ξ' (t • u' + g + c • u) = ξ' (t • u' + g) := by
  classical
  have hy : T (c • u) ξ' ∈ orbitClosure ξ :=
    Nivat.Colle.mem_orbitClosure_trans hξ' (T_mem_orbitClosure ξ' (c • u))
  -- every parameter `t₀ - k` at which `g - k•u'` is an actual point of `S` is covered by Step B
  have hlow : ∀ k : ℕ, g - (k : ℤ) • u' ∈ S →
      ξ' ((t₀ - (k : ℤ)) • u' + g + c • u) = ξ' ((t₀ - (k : ℤ)) • u' + g) := by
    intro k hk
    have h := hbase _ hk
    rwa [shift_sub_smul] at h
  -- the induction proper
  have key : ∀ m : ℕ,
      ξ' ((t₀ + (m : ℤ)) • u' + g + c • u) = ξ' ((t₀ + (m : ℤ)) • u' + g) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      have htm : τ ≤ t₀ + (m : ℤ) := by omega
      -- every point of the window other than `g` is already known, so `g` follows
      have hagr : ∀ z ∈ S.erase g,
          ξ' ((t₀ + (m : ℤ)) • u' + z) = T (c • u) ξ' ((t₀ + (m : ℤ)) • u' + z) := by
        intro z hz
        have hzS : z ∈ S := Finset.mem_of_mem_erase hz
        have hzne : z ≠ g := Finset.ne_of_mem_erase hz
        show ξ' ((t₀ + (m : ℤ)) • u' + z) = ξ' ((t₀ + (m : ℤ)) • u' + z + c • u)
        by_cases hzQ : z ∈ Q
        · -- the `Q`-part: `hQR` puts both positions in `R`, `hRper` moves across `c•u`
          obtain ⟨hmem, hmem'⟩ := hQR (t₀ + (m : ℤ)) htm z hzQ
          exact (hRper _ hmem hmem').symm
        · -- the edge part: `z` sits at `g - k•u'`, `k ≥ 1`, i.e. at an earlier parameter
          obtain ⟨k, hzeq⟩ := hedge z hzS hzQ
          have hk0 : k ≠ 0 := fun h => hzne (by simpa [h] using hzeq)
          have hD : ξ' ((t₀ + (m : ℤ) - (k : ℤ)) • u' + g + c • u)
              = ξ' ((t₀ + (m : ℤ) - (k : ℤ)) • u' + g) := by
            rcases le_or_gt (k : ℕ) m with hkm | hkm
            · -- the parameter is still `≥ t₀`: strong induction hypothesis
              have h := ih (m - k) (by omega)
              have he : t₀ + ((m - k : ℕ) : ℤ) = t₀ + (m : ℤ) - (k : ℤ) := by omega
              rwa [he] at h
            · -- the parameter dropped below `t₀`: Step B, at the intermediate edge point
              have hmemS : g - ((k - m : ℕ) : ℤ) • u' ∈ S :=
                hSseg (k - m) k (by omega) (hzeq ▸ hzS)
              have h := hlow (k - m) hmemS
              have he : t₀ - ((k - m : ℕ) : ℤ) = t₀ + (m : ℤ) - (k : ℤ) := by omega
              rwa [he] at h
          rw [hzeq, shift_sub_smul]
          exact hD.symm
      have h := generatesAt_translate hgen hξ' hy ((t₀ + (m : ℤ)) • u') hagr
      exact h.symm
  intro t ht
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, t = t₀ + (m : ℤ) := ⟨(t - t₀).toNat, by omega⟩
  exact key m

end Nivat.Claim47
