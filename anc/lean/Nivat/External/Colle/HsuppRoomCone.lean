/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.PolyChain
import Nivat.External.Colle.L1LineEdgePackage
import Nivat.External.Colle.L1EdgeFace
import Nivat.External.Colle.RegionTranslate
import Nivat.External.Colle.HsuppTowerBase

/-!
# `hsupp_room_cone` — `Sphi − a` lies in the cone spanned by `w` and the fan-neighbour edge

Lane `lane-hsupp`, dispatched by team-lead 2026-09-22, helping lane-place with `hroomT`
(`RegionSteps.lean:1748-1755`, the last piece of `hcover`).

## Setup and sign conventions (pinned by a numeric check on the standard hexagon,
`h = ((-2,0),(1,2),(-1,2))`, `Sphi` the hexagon `(0,0),(1,2),(0,4),(-2,4),(-3,2),(-2,0)`)

`a` is the `-w` end of `Sphi`'s `m`-lowest face: `a ∈ Sphi`, `a` minimises `dot m` (`ha_min`),
and every other point at the same `m`-level is `a + t • w` for `t : ℕ` (`ha_end`) — this pins
`a` to be literally `faceStart Sphi (-m)` (`a_eq_faceStart` below), given the standard
`NOTATION.md` convention `w = dir (-m)` (`hw_eq`; checked on the hexagon: `m = (0,1)`,
`-m = (0,-1)` is the bottom edge's outward normal, `w = dir (-m) = (1,0)`, matching `a = (-2,0)`,
`b = (0,0) = a + 2 • w`).

`ν` is `Sphi`'s edge normal fan-adjacent to `-m` on the *other* side from the bottom edge
(`0 < det ν (-m)`, nothing strictly between — the same adjacency shape as
`HsuppTowerBase.b0pt_face_facts`/Lemma H). `PolyChain.adjacent_shared_vertex` gives
`a = faceEnd Sphi ν`. The cone direction along *that* edge, from `a`, is **`-dir ν`**, not
`dir ν` — checked on the hexagon: `ν = (-2,-1)` (the edge `(-3,2) → (-2,0)`'s outward normal),
`dir ν = (1,-2)` is the direction *arriving* at `a`; the edge leaves `a` towards `(-3,2)` in
direction `(-1,2) = -dir ν`. (This sign is exactly the "`faceEnd` vs `faceStart`" distinction:
`a` is the *far* end of `face Sphi ν` in the `dir ν` direction, so the rest of that face is
*behind* `a`, i.e. reached by subtracting nonnegative multiples of `dir ν`.)

With `e := -dir ν`: `det w e > 0` (from `hdet_order : 0 < det ν (-m)`, via the rotation
identity `det (dir a) (dir b) = det a b`), and for every `b ∈ Sphi`: `dot m (b-a) ≥ 0`
(`ha_min`) translates to `det w (b-a) ≥ 0` (since `m = dir w` exactly, `dir ∘ dir = -id` on
`w = dir (-m)`), and `dot ν (b-a) ≤ 0` (`a` maximises `ν` over `Sphi`, being `faceEnd Sphi ν`)
translates to `det e (b-a) ≤ 0` (since `ν = dir e` exactly). Feeding both into
`L1LinePackage.cramer_decomp`'s `(w, e)`-basis expansion of `b - a` gives both coefficients
`≥ 0` — checked on the hexagon: `b = (1,2)`, `b - a = (3,2) = 4 • (1,0) + 1 • (-1,2)`.

## Status

0 sorry, axiom-clean.
-/

set_option autoImplicit false

namespace Nivat.HsuppRoomCone

open Nivat Nivat.LE2 Nivat.PolyChain Nivat.L1LinePackage Nivat.Colle35 Nivat.HsuppTowerBase

/-! ## Part 0: the rotation-invariance of `det` under `dir`, and `dir ∘ dir = -id` -/

theorem det_dir_dir (a b : ℤ × ℤ) : det (dir a) (dir b) = det a b := by
  simp only [det, dir]; ring

theorem dir_dir (a : ℤ × ℤ) : dir (dir a) = -a := by
  ext <;> simp [dir]

/-- The far end of a face (`faceStart + faceLen • dir ν`) maximises `dot (dir ν)` over the
whole face. (Local copy — `HsuppTowerBase.faceEnd_maxdir` lives in an un-landed `tmp/wip` file
and cannot be imported here.) -/
theorem faceEnd_maxdir_local {T : Set (ℤ × ℤ)} {ν w : ℤ × ℤ} (hlc : Nivat.IsLatticeConvexRegion T)
    (hfin : T.Finite) (hν : ν ∈ E T) (hdirν : dir ν = w) :
    ∀ z ∈ face T ν, dot w z ≤ dot w (faceStart T ν + (faceLen T ν : ℤ) • dir ν) := by
  subst hdirν
  intro z hz
  rw [face_eq_segment hlc hfin hν] at hz
  obtain ⟨t, htle, htz⟩ := hz
  have hexpand : ∀ s : ℤ, dot (dir ν) (faceStart T ν + s • dir ν)
      = dot (dir ν) (faceStart T ν) + s * dot (dir ν) (dir ν) := by
    intro s
    simp only [dot, dir, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [htz, hexpand, hexpand]
  have htcast : (t : ℤ) ≤ (faceLen T ν : ℤ) := by exact_mod_cast htle
  have hQnonneg : 0 ≤ dot (dir ν) (dir ν) := by
    simp only [dot]; exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right htcast hQnonneg]

theorem w_ne_zero_of_dir_neg_m {m w : ℤ × ℤ} (hw_eq : w = dir (-m)) (hm_ne : m ≠ 0) : w ≠ 0 := by
  rw [hw_eq]
  intro h
  apply hm_ne
  have hd : dir (dir (-m)) = dir (0 : ℤ × ℤ) := congrArg dir h
  rw [dir_dir] at hd
  have h0 : dir (0 : ℤ × ℤ) = (0 : ℤ × ℤ) := by simp [dir]
  rw [h0] at hd
  simpa using hd

/-- `m = dir w` exactly, when `w = dir (-m)` (pure algebra: `dir ∘ dir = -id`). -/
theorem m_eq_dir_w {m w : ℤ × ℤ} (hw_eq : w = dir (-m)) : m = dir w := by
  rw [hw_eq, dir_dir]; ring

/-! ## Part 1: pinning `a = faceStart Sphi (-m)` -/

/-- `a` (minimal for `dot m`, with `ha_end`'s "every same-level point is `a + t•w`") is exactly
`faceStart S (-m)`. -/
theorem a_eq_faceStart {S : Set (ℤ × ℤ)} (hSfin : S.Finite) (hSconv : Nivat.IsLatticeConvexRegion S)
    {m w a : ℤ × ℤ}
    (hw_eq : w = dir (-m)) (hw_ne : w ≠ 0)
    (hnegm_ES : -m ∈ E S) (ha_mem : a ∈ S)
    (ha_min : ∀ b ∈ S, dot m a ≤ dot m b)
    (ha_end : ∀ b ∈ S, dot m b = dot m a → ∃ t : ℕ, b = a + (t : ℤ) • w) :
    a = faceStart S (-m) := by
  have ha_face : a ∈ face S (-m) := mem_face_iff.mpr ⟨ha_mem, fun y hy => by
    have h := ha_min y hy
    rw [dot_neg_left, dot_neg_left]; linarith⟩
  have hstart_face : faceStart S (-m) ∈ face S (-m) := faceStart_mem hSfin hnegm_ES
  have heq_val : dot m (faceStart S (-m)) = dot m a := by
    have h1 := (mem_face_iff.mp ha_face).2 (faceStart S (-m)) (face_subset S (-m) hstart_face)
    have h2 := (mem_face_iff.mp hstart_face).2 a (face_subset S (-m) ha_face)
    rw [dot_neg_left, dot_neg_left] at h1 h2
    linarith
  obtain ⟨t0, ht0⟩ :=
    ha_end (faceStart S (-m)) (face_subset S (-m) hstart_face) heq_val
  rw [face_eq_segment hSconv hSfin hnegm_ES] at ha_face
  obtain ⟨s, _, hs⟩ := ha_face
  rw [← hw_eq] at hs
  -- `hs : a = faceStart S (-m) + s • w`, `ht0 : faceStart S (-m) = a + t0 • w`.
  rw [ht0] at hs
  have hsum : ((t0 : ℤ) + (s : ℤ)) • w = (0 : ℤ × ℤ) :=
    add_left_cancel (a := a) (by rw [add_smul, ← add_assoc, ← hs, add_zero])
  have hst0 : s = 0 ∧ t0 = 0 := by
    have hwor : w.1 ≠ 0 ∨ w.2 ≠ 0 := by
      by_contra hcon; push Not at hcon
      exact hw_ne (Prod.ext hcon.1 hcon.2)
    have hcoef : (t0 : ℤ) + (s : ℤ) = 0 := by
      rcases hwor with h1 | h2
      · have := congrArg Prod.fst hsum
        simp only [Prod.smul_fst, smul_eq_mul, Prod.fst_zero] at this
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd h h1
      · have := congrArg Prod.snd hsum
        simp only [Prod.smul_snd, smul_eq_mul, Prod.snd_zero] at this
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd h h2
    constructor <;> omega
  rw [ht0, hst0.2]
  simp

/-! ## Part 2: the cone containment -/

theorem dot_dir_eq_det (v z : ℤ × ℤ) : dot (dir v) z = det v z := by
  simp only [dot, dir, det]; ring

theorem det_dir_eq_neg_dot (v z : ℤ × ℤ) : det (dir v) z = - dot v z := by
  simp only [det, dir, dot]; ring

/-- **Main theorem.** `Sphi - a` lies in the cone spanned by `w` and `-dir ν`, with
nonnegative real coefficients. `w := dir (-m)` (the bottom-edge direction), `ν` the
fan-neighbouring edge normal with `0 < det ν (-m)` and nothing strictly between (`hadj`),
`a` pinned to `faceStart Sphi (-m) = faceEnd Sphi ν` via `a_eq_faceStart` +
`adjacent_shared_vertex`. -/
theorem sphi_sub_a_mem_cone {S : Set (ℤ × ℤ)} (hSfin : S.Finite)
    (hSconv : Nivat.IsLatticeConvexRegion S)
    {m w ν a : ℤ × ℤ}
    (hw_eq : w = dir (-m)) (hm_ne : m ≠ 0)
    (hnegm_ES : -m ∈ E S) (ha_mem : a ∈ S)
    (ha_min : ∀ b ∈ S, dot m a ≤ dot m b)
    (ha_end : ∀ b ∈ S, dot m b = dot m a → ∃ t : ℕ, b = a + (t : ℤ) • w)
    (hν_ES : ν ∈ E S)
    (hdet_order : 0 < det ν (-m))
    (hadj : ∀ μ ∈ E S, ¬ (0 < det ν μ ∧ 0 < det μ (-m))) :
    ∀ b ∈ S, ∃ p q : ℝ, 0 ≤ p ∧ 0 ≤ q ∧
      toReal (b - a) = p • toReal w + q • toReal (- dir ν) := by
  have hw_ne : w ≠ 0 := w_ne_zero_of_dir_neg_m hw_eq hm_ne
  have haStart : a = faceStart S (-m) :=
    a_eq_faceStart hSfin hSconv hw_eq hw_ne hnegm_ES ha_mem ha_min ha_end
  have hshared := adjacent_shared_vertex hSfin hSconv hν_ES hnegm_ES hdet_order hadj
  have haEnd : a = faceStart S ν + (faceLen S ν : ℤ) • dir ν := by rw [haStart, hshared]
  set e : ℤ × ℤ := - dir ν with he_def
  -- `ν = dir e` exactly (`dir ∘ dir = -id`).
  have hν_eq : ν = dir e := by rw [he_def]; ext <;> simp [dir]
  have hm_eq : m = dir w := m_eq_dir_w hw_eq
  -- `a` maximises both `dot m` (backwards: `ha_min`) and `dot ν` over `S`.
  have ha_mem_negm : a ∈ face S (-m) := haStart ▸ faceStart_mem hSfin hnegm_ES
  have ha_mem_ν : a ∈ face S ν := by
    rw [haEnd]; exact faceEnd_mem hSconv hSfin hν_ES
  -- `det w e > 0` and the sign facts.
  have hdet_we_pos : 0 < det w e := by
    have h1 : det w e = - det (dir (-m)) (dir ν) := by rw [hw_eq, he_def]; simp [det]; ring
    have h2 : det (dir (-m)) (dir ν) = det (-m) ν := det_dir_dir (-m) ν
    have h3 : det (-m) ν = - det ν (-m) := by
      have := det_skew ν (-m); linarith [this]
    rw [h2, h3] at h1
    have : det w e = det ν (-m) := by rw [h1]; ring
    rw [this]; exact hdet_order
  have hdet_we_ne : det w e ≠ 0 := ne_of_gt hdet_we_pos
  intro b hb
  have hmb : dot m (b - a) ≥ 0 := by
    have := ha_min b hb
    simp only [dot, Prod.fst_sub, Prod.snd_sub]
    simp only [dot] at this
    linarith
  have hνb : dot ν (b - a) ≤ 0 := by
    have h := (mem_face_iff.mp ha_mem_ν).2 b hb
    simp only [dot, Prod.fst_sub, Prod.snd_sub]
    simp only [dot] at h
    linarith
  -- translate to `det` facts via the `dir` identities.
  have hdetw : det w (b - a) ≥ 0 := by
    rw [← dot_dir_eq_det w (b - a), ← hm_eq]; exact hmb
  have hdete : det (b - a) e ≥ 0 := by
    have h1 : det (b - a) e = - det (b - a) (dir ν) := by rw [he_def]; simp [det]; ring
    have h2 : det (b - a) (dir ν) = - det (dir ν) (b - a) := by
      have := det_skew (dir ν) (b - a); linarith [this]
    have h3 : det (dir ν) (b - a) = - dot ν (b - a) := det_dir_eq_neg_dot ν (b - a)
    rw [h2, h3] at h1
    linarith
  have hdecomp := cramer_decomp hdet_we_ne (b - a)
  refine ⟨(det (b - a) e : ℝ) / (det w e : ℝ), (det w (b - a) : ℝ) / (det w e : ℝ),
    div_nonneg (by exact_mod_cast hdete) (le_of_lt (by exact_mod_cast hdet_we_pos)),
    div_nonneg (by exact_mod_cast hdetw) (le_of_lt (by exact_mod_cast hdet_we_pos)), ?_⟩
  simpa [he_def] using hdecomp

end Nivat.HsuppRoomCone

#print axioms Nivat.HsuppRoomCone.det_dir_dir
#print axioms Nivat.HsuppRoomCone.dir_dir
#print axioms Nivat.HsuppRoomCone.faceEnd_maxdir_local
#print axioms Nivat.HsuppRoomCone.w_ne_zero_of_dir_neg_m
#print axioms Nivat.HsuppRoomCone.m_eq_dir_w
#print axioms Nivat.HsuppRoomCone.a_eq_faceStart
#print axioms Nivat.HsuppRoomCone.dot_dir_eq_det
#print axioms Nivat.HsuppRoomCone.det_dir_eq_neg_dot
#print axioms Nivat.HsuppRoomCone.sphi_sub_a_mem_cone
