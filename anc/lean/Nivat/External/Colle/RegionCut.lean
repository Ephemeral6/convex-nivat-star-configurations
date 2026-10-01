/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.RegionSemiInfUnique
import Nivat.External.Colle.RegionCutLeftEdge
import Nivat.Section8.RegionUpgrade

/-!
# `IsRegion` is stable under cutting by `halfPlaneLE n' c`

Colle, Lemma 4.1 (`scratch/b3_colle2.txt:694`, `:700`) concludes on
`𝒦 = ℋ(ℓ_{Q'}) ∩ ℛ`, where `ℛ` is an `(ℓ,ℓ')`-region and the cutting line is parallel
to the `ℓ'`-edge.  This file proves the corresponding closure property of
`LE2.IsRegion` (`LatticeEdges.lean:2221`, Colle Definition 3.1):

    isRegion_inter_halfPlaneLE :
      IsRegion R n n' → z₀ ∈ R → dot n' z₀ = c → IsRegion (R ∩ halfPlaneLE n' c) n n'

The orientation is **not** a free choice.  Cutting by `halfPlaneGE n' c` is refuted in
`RegionHalfPlaneOrientation.lean` (`not_isRegion_inter_halfPlaneGE`): it truncates the
`n`-edge to two points.  The cut must have outer normal `n'` itself, and it does not
destroy the `n'`-edge — it slides it down to level `c` (`face_inter_slice`,
`RegionEdges.lean:630`).

## What was already available

Of Definition 3.1's nine fields, six are discharged by `isRegion_of_two_semiInf`
(`RegionEdges.lean:553`), and a seventh (`semiInfUnique`) by
`semiInfUnique_of_two_semiInf` (`RegionSemiInfUnique.lean`).  So `isRegion_of_two_semiInf'`
reduces the goal to three inputs:

* **lattice convexity** — `isLatticeConvexRegion_inter_halfPlaneLE` (`RegionEdges.lean:656`);
* **the `n`-edge** — `isSemiInfEdge_inter_halfPlaneLE_left` (`RegionCutLeftEdge.lean`),
  which needs no geometry: `dot n` is constant on `face R n` and `dot n'` is bounded above
  on `R`, so the discarded points sit in a `finite_of_dot_bounded` box;
* **the `n'`-edge** — the content of this file.

## The `n'`-edge (§1–§3 below)

This is the genuine two-dimensional step, and it is *not* the mirror image of the
`n`-edge.  The cut creates a face at a level `c` where `R` previously had no face at
all, so `face (R ∩ ℋ) n'` is the whole slice `{z ∈ R : ⟨n', z⟩ = c}`, a set unrelated to
`face R n'`.  Infinitude has to be **manufactured** at the new level, not preserved.

The route:

1. **Ray extraction** (§1).  `face R n'` lies on the lattice line `⟨n', ·⟩ = const`,
   which `Prim n'` parameterises by `dir n'` (`exists_zsmul_dir_of_mem_face`).  Lattice
   convexity makes the parameter set order-convex in `ℤ` (`mem_of_between`), and an
   infinite order-convex subset of `ℤ` contains a ray
   (`exists_ray_of_infinite_intConvex`).  The resulting direction is `± dir n'`, hence
   automatically orthogonal to `n'`.
2. **Promotion to a recession direction** (§2).  `toReal_mem_recCone_of_nat_ray`
   (`Section8/RegionUpgrade.lean:103`).  The `ℤ → ℝ` interpolation and the closedness
   limit are already inside that lemma.
3. **Transport** (§2).  `add_mem_of_mem_recCone` (`Section8/RegionUpgrade.lean:138`)
   translates *every* point of `R` along the direction — in particular `z₀`, which sits
   at the new level `c`.  Since the direction is orthogonal to `n'`, the whole orbit
   stays at level `c`.

Note that `not_E_inter_subset` (`RegionEdges.lean:740`) shows `E(R ∩ ℋ) ⊆ E R ∪ {k}` is
**false**: cutting really does create new edge directions.  That hazard is routed
around rather than repaired — the new edges are necessarily *finite*, and `IsRegion`
only constrains semi-infinite ones, which is exactly what `semiInfUnique_of_two_semiInf`
exploits.
-/

namespace Nivat.LE2

open Nivat

/-! ### Name probes.  Every external lemma used below is `#check`ed here. -/

section Probes
#check @Set.finite_Icc
#check @Set.Infinite.nonempty
#check @Set.Infinite.nontrivial
#check @Set.Infinite.mono
#check @Set.Infinite.of_image
#check @Set.infinite_of_injective_forall_mem
#check @add_div
#check @div_mul_eq_mul_div
#check @div_eq_iff
#check @div_self
#check @div_nonneg
#check @mul_right_cancel₀
#check @Nat.gcd_comm
-- `Nivat.Defs.Complexity` / `Nivat.Section8.HalfPlane` / `Nivat.Section8.RegionUpgrade`
#check @toReal
#check @toReal_add
#check @toReal_zsmul
#check @convex_convHullOf
#check @mem_convHullOf_of_mem
#check @eq_preimage_convHullOf
#check @recCone
#check @toReal_mem_recCone_of_nat_ray
#check @add_mem_of_mem_recCone
-- `Nivat.External.Colle.LatticeEdges`
#check @Prim
#check @Prim.ne_zero
#check @dir
#check @dot_dir
#check @det_eq_zero_of_dot_eq_zero
#check @exists_smul_of_det_eq_zero
#check @dot_sub_eq_zero_of_mem_face
#check @IsSemiInfEdge
#check @IsRegion
-- `Nivat.External.Colle.RegionEdges` and the two new files
#check @face_inter_slice
#check @isLatticeConvexRegion_inter_halfPlaneLE
#check @isRegion_of_two_semiInf'
#check @isSemiInfEdge_inter_halfPlaneLE_left
end Probes

/-! ## §0. An infinite convex subset of `ℤ` contains a ray

The only genuinely combinatorial ingredient, and the only place where infinitude is
converted into a *uniform* statement.  Pure `ℤ`; no geometry. -/

/-- `S ⊆ ℤ` is *order convex*: it contains every integer between two of its members.
This is the one-dimensional trace of lattice convexity along a lattice line. -/
def IntConvex (S : Set ℤ) : Prop := ∀ a ∈ S, ∀ b ∈ S, ∀ t : ℤ, a ≤ t → t ≤ b → t ∈ S

/-- **An infinite order-convex set of integers contains a ray.**
If `S` were bounded in both directions it would sit inside a finite `Set.Icc`. -/
theorem exists_ray_of_infinite_intConvex {S : Set ℤ} (hconv : IntConvex S)
    (hinf : S.Infinite) :
    (∃ a, ∀ t : ℤ, a ≤ t → t ∈ S) ∨ (∃ a, ∀ t : ℤ, t ≤ a → t ∈ S) := by
  obtain ⟨a, ha⟩ := hinf.nonempty
  by_cases hup : ∀ t : ℤ, ∃ b ∈ S, t ≤ b
  · refine Or.inl ⟨a, fun t hat => ?_⟩
    obtain ⟨b, hb, htb⟩ := hup t
    exact hconv a ha b hb t hat htb
  · refine Or.inr ⟨a, fun t hta => ?_⟩
    simp only [not_forall, not_exists, not_and, not_le] at hup
    obtain ⟨u, hu⟩ := hup
    have hdown : ∀ s : ℤ, ∃ b ∈ S, b ≤ s := by
      intro s
      by_contra hc
      simp only [not_exists, not_and, not_le] at hc
      refine hinf ((Set.finite_Icc (s + 1) (u - 1)).subset fun z hz => ?_)
      have h1 := hc z hz
      have h2 := hu z hz
      exact ⟨by omega, by omega⟩
    obtain ⟨b, hb, hbt⟩ := hdown t
    exact hconv b hb a ha t hbt hta

/-! ## §1. Extracting a lattice ray from an infinite face -/

/-- Arithmetic of `dot` along a line. -/
theorem dot_add_zsmul (n q e : ℤ × ℤ) (t : ℤ) :
    dot n (q + t • e) = dot n q + t * dot n e := by
  simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem dot_neg_right (n e : ℤ × ℤ) : dot n (-e) = - dot n e := by
  simp only [dot, Prod.fst_neg, Prod.snd_neg]
  ring

/-- The direction of a primitive normal is primitive. -/
theorem prim_dir_of_prim {n : ℤ × ℤ} (h : Prim n) : Prim (dir n) := by
  have h1 : Int.gcd (dir n).1 (dir n).2 = Nat.gcd n.2.natAbs n.1.natAbs := by
    simp [dir, Int.gcd]
  have h2 : Int.gcd n.1 n.2 = Nat.gcd n.1.natAbs n.2.natAbs := by simp [Int.gcd]
  show Int.gcd (dir n).1 (dir n).2 = 1
  rw [h1, Nat.gcd_comm, ← h2]
  exact h

/-- **A face is a lattice segment in the direction `dir n`.**  Two points of one face
differ by an *integer* multiple of `dir n`.  This is where primitivity of the normal is
used: for a non-primitive normal the parameterisation would skip lattice points, and the
parameter set below would not be order-convex. -/
theorem exists_zsmul_dir_of_mem_face {R : Set (ℤ × ℤ)} {n a z : ℤ × ℤ} (hn : Prim n)
    (ha : a ∈ face R n) (hz : z ∈ face R n) : ∃ t : ℤ, z = a + t • dir n := by
  have hd0 : dot n (z - a) = 0 := dot_sub_eq_zero_of_mem_face ha hz
  have hdd : dot n (dir n) = 0 := dot_dir n
  have hdet : det (dir n) (z - a) = 0 := det_eq_zero_of_dot_eq_zero hn.ne_zero hdd hd0
  obtain ⟨t, ht⟩ := exists_smul_of_det_eq_zero (prim_dir_of_prim hn) hdet
  refine ⟨t, ?_⟩
  have h1 : z.1 - a.1 = t * (dir n).1 := by
    have := congrArg Prod.fst ht; simpa using this
  have h2 : z.2 - a.2 = t * (dir n).2 := by
    have := congrArg Prod.snd ht; simpa using this
  refine Prod.ext ?_ ?_ <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  · rw [← h1]; ring
  · rw [← h2]; ring

/-- The convex-combination identity, in coordinate-free form. -/
theorem convex_comb_line {X Y : ℝ × ℝ} {A B s u t : ℝ} (hAB : A + B = 1)
    (hcoef : A * s + B * u = t) :
    A • (X + s • Y) + B • (X + u • Y) = X + t • Y := by
  rw [smul_add, smul_add, smul_smul, smul_smul,
    show A • X + (A * s) • Y + (B • X + (B * u) • Y)
        = (A + B) • X + (A * s + B * u) • Y by rw [add_smul, add_smul]; abel,
    hAB, hcoef, one_smul]

/-- **Lattice convexity along a line.**  A lattice point lying between two points of `R`
on a common line is itself in `R`.  This is the only place `IsLatticeConvexRegion` is
unfolded, via `eq_preimage_convHullOf` (`Section8/HalfPlane.lean:182`). -/
theorem mem_of_between {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R) {q e : ℤ × ℤ}
    {s t u : ℤ} (hs : q + s • e ∈ R) (hu : q + u • e ∈ R) (h1 : s ≤ t) (h2 : t ≤ u) :
    q + t • e ∈ R := by
  rcases eq_or_lt_of_le (h1.trans h2) with heq | hlt
  · have ht : t = s := by omega
    rw [ht]; exact hs
  have hsu : (s : ℝ) < (u : ℝ) := by exact_mod_cast hlt
  have hDne : ((u : ℝ) - (s : ℝ)) ≠ 0 := by linarith
  have hts : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast h1
  have htu : (t : ℝ) ≤ (u : ℝ) := by exact_mod_cast h2
  have hA0 : (0 : ℝ) ≤ ((u : ℝ) - (t : ℝ)) / ((u : ℝ) - (s : ℝ)) :=
    div_nonneg (by linarith) (by linarith)
  have hB0 : (0 : ℝ) ≤ ((t : ℝ) - (s : ℝ)) / ((u : ℝ) - (s : ℝ)) :=
    div_nonneg (by linarith) (by linarith)
  have hAB : ((u : ℝ) - (t : ℝ)) / ((u : ℝ) - (s : ℝ))
      + ((t : ℝ) - (s : ℝ)) / ((u : ℝ) - (s : ℝ)) = 1 := by
    rw [← add_div,
      show (u : ℝ) - (t : ℝ) + ((t : ℝ) - (s : ℝ)) = (u : ℝ) - (s : ℝ) by ring,
      div_self hDne]
  have hcoef : ((u : ℝ) - (t : ℝ)) / ((u : ℝ) - (s : ℝ)) * (s : ℝ)
      + ((t : ℝ) - (s : ℝ)) / ((u : ℝ) - (s : ℝ)) * (u : ℝ) = (t : ℝ) := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hDne]
    ring
  have hexp : ∀ m : ℤ, toReal (q + m • e) = toReal q + (m : ℝ) • toReal e := by
    intro m; rw [toReal_add, toReal_zsmul]
  have hmem := (convex_convHullOf R) (mem_convHullOf_of_mem hs) (mem_convHullOf_of_mem hu)
    hA0 hB0 hAB
  rw [hexp s, hexp u, convex_comb_line hAB hcoef, ← hexp t] at hmem
  rw [eq_preimage_convHullOf hR]
  exact hmem

/-- **Ray extraction.**  An infinite face of a lattice-convex region contains a full
lattice ray.  The direction is `± dir n`, hence automatically orthogonal to `n`. -/
theorem exists_nat_ray_of_infinite_face {R : Set (ℤ × ℤ)} {n : ℤ × ℤ}
    (hR : IsLatticeConvexRegion R) (hn : Prim n) (hinf : (face R n).Infinite) :
    ∃ q e : ℤ × ℤ, e ≠ 0 ∧ dot n e = 0 ∧ ∀ k : ℕ, q + (k : ℤ) • e ∈ R := by
  obtain ⟨a, ha⟩ := hinf.nonempty
  have hdp : Prim (dir n) := prim_dir_of_prim hn
  have hd0 : dir n ≠ 0 := hdp.ne_zero
  have hdn : dot n (dir n) = 0 := dot_dir n
  have hdisj : (∃ t₀ : ℤ, ∀ t : ℤ, t₀ ≤ t → a + t • dir n ∈ face R n) ∨
      (∃ t₀ : ℤ, ∀ t : ℤ, t ≤ t₀ → a + t • dir n ∈ face R n) := by
    refine exists_ray_of_infinite_intConvex
      (S := {t : ℤ | a + t • dir n ∈ face R n}) ?_ ?_
    · intro s hs u hu t hst htu
      have hsR : a + s • dir n ∈ R := hs.1
      have huR : a + u • dir n ∈ R := hu.1
      refine ⟨mem_of_between hR hsR huR hst htu, fun y hy => ?_⟩
      rw [dot_add_zsmul, hdn, mul_zero, add_zero]
      exact ha.2 y hy
    · refine Set.Infinite.of_image (fun t : ℤ => a + t • dir n) (hinf.mono ?_)
      intro z hz
      obtain ⟨t, rfl⟩ := exists_zsmul_dir_of_mem_face hn ha hz
      exact ⟨t, hz, rfl⟩
  rcases hdisj with ⟨t₀, h⟩ | ⟨t₀, h⟩
  · refine ⟨a + t₀ • dir n, dir n, hd0, hdn, fun k => ?_⟩
    have hk := h (t₀ + (k : ℤ)) (by omega)
    have heq : a + (t₀ + (k : ℤ)) • dir n = a + t₀ • dir n + (k : ℤ) • dir n := by
      rw [add_smul]; abel
    rw [heq] at hk
    exact hk.1
  · refine ⟨a + t₀ • dir n, -dir n, neg_ne_zero.mpr hd0,
      by rw [dot_neg_right, hdn, neg_zero], fun k => ?_⟩
    have hk := h (t₀ - (k : ℤ)) (by omega)
    have heq : a + (t₀ - (k : ℤ)) • dir n = a + t₀ • dir n + (k : ℤ) • (-dir n) := by
      rw [sub_smul, smul_neg]; abel
    rw [heq] at hk
    exact hk.1

/-! ## §2. From a ray to an infinite slice at a *new* level

The step that has no analogue for the `n`-edge: the cut creates a face at a level where
`R` previously had none, so infinitude has to be produced rather than preserved.  The
ray of §1 becomes a recession direction, which then translates *every* point of `R`. -/

/-- **The new face is infinite.**  A non-zero recession direction `e` orthogonal to `n'`
sweeps `z₀` along the level set `{⟨n', ·⟩ = c}` without ever leaving `R`. -/
theorem infinite_slice_of_recCone {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R)
    {e : ℤ × ℤ} (he : e ≠ 0) (hrec : toReal e ∈ recCone R)
    {n' z₀ : ℤ × ℤ} (hz₀ : z₀ ∈ R) (hen : dot n' e = 0) {c : ℤ} (hc : dot n' z₀ = c) :
    {z : ℤ × ℤ | z ∈ R ∧ dot n' z = c}.Infinite := by
  have hstep : ∀ k : ℕ, z₀ + (k : ℤ) • e ∈ R := by
    intro k
    induction k with
    | zero => simpa using hz₀
    | succ m ih =>
        have h := add_mem_of_mem_recCone hR hrec ih
        have heq : z₀ + (m : ℤ) • e + e = z₀ + ((m + 1 : ℕ) : ℤ) • e := by
          push_cast
          rw [add_smul, one_smul]
          abel
        rwa [heq] at h
  have he' : e.1 ≠ 0 ∨ e.2 ≠ 0 := by
    by_contra hcon
    simp only [not_or, not_not] at hcon
    exact he (Prod.ext (by simpa using hcon.1) (by simpa using hcon.2))
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => z₀ + (k : ℤ) • e) ?_ ?_
  · intro x y hxy
    simp only [add_right_inj] at hxy
    have h1 : (x : ℤ) * e.1 = (y : ℤ) * e.1 := by
      have := congrArg Prod.fst hxy; simpa using this
    have h2 : (x : ℤ) * e.2 = (y : ℤ) * e.2 := by
      have := congrArg Prod.snd hxy; simpa using this
    have hxyz : (x : ℤ) = (y : ℤ) := by
      rcases he' with h | h
      · exact mul_right_cancel₀ h h1
      · exact mul_right_cancel₀ h h2
    exact_mod_cast hxyz
  · intro k
    exact ⟨hstep k, by rw [dot_add_zsmul, hen, mul_zero, add_zero, hc]⟩

/-! ## §3. The `n'`-edge survives the cut, and the main theorem -/

/-- **`semiInf'` for the cut region.**  The `n'`-edge is not destroyed by the cut: it
slides down to the cutting level `c` and is still infinite there. -/
theorem isSemiInfEdge_inter_halfPlaneLE_right {R : Set (ℤ × ℤ)} {n n' : ℤ × ℤ}
    (hR : IsRegion R n n') {c : ℤ} {z₀ : ℤ × ℤ} (hz₀ : z₀ ∈ R) (hc : dot n' z₀ = c) :
    IsSemiInfEdge (R ∩ halfPlaneLE n' c) n' := by
  obtain ⟨q, e, he0, hen, hray⟩ :=
    exists_nat_ray_of_infinite_face hR.latticeConvex hR.semiInf'.1.1 hR.semiInf'.2
  have hrec : toReal e ∈ recCone R := toReal_mem_recCone_of_nat_ray hray
  have hinf : (face (R ∩ halfPlaneLE n' c) n').Infinite := by
    rw [face_inter_slice hz₀ hc]
    exact infinite_slice_of_recCone hR.latticeConvex he0 hrec hz₀ hen hc
  exact ⟨⟨hR.semiInf'.1.1, hinf.nontrivial⟩, hinf⟩

/-- **Colle, Lemma 4.1, the region step.**  Cutting an `(n,n')`-region by the half-plane
with outer normal `n'` through a point `z₀ ∈ R` again gives an `(n,n')`-region — with the
*same* pair of normals.

The hypotheses `hz₀`, `hc` say exactly that the cutting line meets `R`; without them the
intersection can be empty.  The orientation is forced: see
`not_isRegion_inter_halfPlaneGE` in `RegionHalfPlaneOrientation.lean`. -/
theorem isRegion_inter_halfPlaneLE {R : Set (ℤ × ℤ)} {n n' : ℤ × ℤ} (hR : IsRegion R n n')
    {c : ℤ} {z₀ : ℤ × ℤ} (hz₀ : z₀ ∈ R) (hc : dot n' z₀ = c) :
    IsRegion (R ∩ halfPlaneLE n' c) n n' :=
  isRegion_of_two_semiInf'
    (isLatticeConvexRegion_inter_halfPlaneLE _ _ hR.latticeConvex)
    (isSemiInfEdge_inter_halfPlaneLE_left hR c)
    (isSemiInfEdge_inter_halfPlaneLE_right hR hz₀ hc)
    hR.detPos

/-! ### Non-vacuity, on the repository's own non-degenerate region -/

/-- `quad` cut at `z₂ ≥ -c` is again a `((-1,0),(0,-1))`-region, for every `c ≤ 0`.
(Named to avoid a collision with `isRegion_quad_inter_halfPlaneLE` in
`RegionHalfPlaneOrientation.lean`, which is the `c = -1` instance proved there by hand;
this one is an instance of the general theorem.) -/
theorem isRegion_quad_cut_halfPlaneLE (c : ℤ) (hc : c ≤ 0) :
    IsRegion (quad ∩ halfPlaneLE ((0 : ℤ), (-1 : ℤ)) c) (-1, 0) (0, -1) :=
  isRegion_inter_halfPlaneLE isRegion_quad
    (z₀ := ((0 : ℤ), -c))
    (by rw [mem_quad]; exact ⟨le_refl 0, by omega⟩)
    (by simp only [dot_e2']; omega)

#print axioms exists_ray_of_infinite_intConvex
#print axioms prim_dir_of_prim
#print axioms exists_zsmul_dir_of_mem_face
#print axioms convex_comb_line
#print axioms mem_of_between
#print axioms exists_nat_ray_of_infinite_face
#print axioms infinite_slice_of_recCone
#print axioms isSemiInfEdge_inter_halfPlaneLE_right
#print axioms isRegion_inter_halfPlaneLE
#print axioms isRegion_quad_cut_halfPlaneLE

end Nivat.LE2
