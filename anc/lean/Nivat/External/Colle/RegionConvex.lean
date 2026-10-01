/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ShellRegion
import Nivat.External.Colle.RegionCutGE

/-!
# When is `Â_∞^{(ε)}` an `(ℓ, ℓ_J)`-region?  The side condition, isolated

`ShellConvex.lean` shows that `IsLatticeConvexRegion (cg.toChainData.shellInf ε)` does **not**
follow from the fields of `ChainDataGeom` — not even under `hRconv` (`cgc`, `ε = 2`).
`Case2WindowProbe.lean` shows it *can* hold: `cgc` at `ε = 1`, and `cgg` at every `ε`.  Both
positive proofs there go through a concrete solved formula for the shell (`mem_shellInf_one`,
`mem_shellInf_cgg`) and exhibit an explicit real polyhedron; they use the concrete
`Kc` / `Kg`, not bundle fields.  But their *shape* is the same, and it generalises.

## The side condition

`MaxEnv.shell_eq_reach_inter` (`ShellLine.lean:43`) splits the shell as

  `Â_∞^{(ε)} = reachSet Â_∞ v_{J-1} ∩ {c_J − ε ≤ ⟪n_J, ·⟫}`,

so the only `ε`-dependence is a half-plane cut, and `LE2.isLatticeConvexRegion_inter_halfPlaneGE`
(`RegionCutGE.lean:24`) says half-plane cuts preserve lattice-convexity.  Hence

  **`hreach : IsLatticeConvexRegion (reachSet (⋃ i, Ahat i) vJ1)`**

is a side condition under which **every** shell is lattice-convex, and with the two free ray
conjuncts of `ShellRegion.lean` every shell is a `Colle41.IsRegion (·) p vJ`
(`ChainDataGeom.isRegion_shellInf_of_reach`).  It is the `ε → ∞` limit of the shells
(`reachSet_eq_iUnion_shellInf`), and it strictly strengthens `hRconv`
(`hRconv_of_reach`; `cgc` has `hRconv` but not `hreach`, since its `ε = 2` shell is not
lattice-convex — `ShellConvex.not_isLatticeConvexRegion_shellInf_cgc_two`).

## What is and is not claimed

* `hreach` is **sufficient**.  The converse "every shell lattice-convex ⇒ `hreach`" is *not*
  proved here: `LE2.isLatticeConvexRegion_iUnion_of_isClosed` would need closedness of the
  union of the hulls, which an increasing union does not supply for free.
* `hreach` is **not a field** of `ChainDataGeom` and is **not derivable** from its fields:
  `cgc` satisfies all of them and fails `hreach`.  What Collé has and the bundle does not
  record is the `ℓ_{J-1}`-edge of `Â_∞` (`E(S_φ)`-envelopedness, `b3_colle2.txt:402,492,504`;
  see `ShellConvex.lean` §3).  **That edge is transcribed below as `EdgeJ1Data` and
  `edge ⇒ hreach` is proved** (`EdgeJ1Data.isLatticeConvexRegion_reachSet`,
  `ChainDataGeom.hreach_of_edgeJ1`, `ChainDataGeom.isRegion_shellInf_of_edgeJ1`), for *any*
  sweep step — the step `⟪n_J, v_{J-1}⟫` is `−1` on `cgg` and `−2` on `cgc`
  (`tmp/step_measure.lean`), so no unimodularity is assumed anywhere.
* **OPEN #9 (2026-09-19 ruling): `EdgeJ1Data` is a standalone structure**, neither a field of
  `ChainDataWithShell` nor a binder of `exists_case2_window`.  `b3_colle2.txt:506` *asserts*
  the enveloping property of `Â_∞`, so its long-run home is a theorem out of leaf A's
  construction; until that exists, `hreach_of_edgeJ1` has **no producer** and this module is
  off the main theorem's import closure.  Recorded as open debt, not as progress.
* Non-vacuity (`PROTOCOL.md` §9): `hreach` — `cgg` (`Case2WindowProbe.Gen`) satisfies it and
  `cgc` does not (`tmp/regionconvex_witness.lean`).  `EdgeJ1Data` — satisfied on the cone
  `Kc' = {y ≥ 0, 2x + y ≥ 0, x − 2y ≥ −5}` with sweep `(1,−2)` (**step 2**), `a₀ = 0`,
  `n_{J-1} = (2,1)`, and the whole theorem instantiates there (`tmp/edge_kcprime.lean`);
  **not** satisfied by `cgg`, `cgc`, `cgn` (their `Â_∞` has no edge parallel to `v_{J-1}`;
  `cgg`'s shells are convex for a different reason).  All receipts **in `tmp/`, not landed**.

## Consumer

`exists_case2_window` (`RegionSteps.lean`), conjunct `Colle41.IsRegion R p cg.vJ` at
`R := cg.toChainData.shellInf ε`.  This file is upstream of `RegionSteps` (`ShellRegion` needs
only `ChainGeom` + `Lemma41`; `RegionCutGE` is already imported by `L3Band`), so
`RegionSteps.lean` can `import` it — **but only once `hreach` (or `EdgeJ1Data`) is
supplied**; see OPEN #9 above.  `hnJv : dot nJ vJ1 < 0` is taken as a binder of the two
bundle wrappers because its proof, `ANormal.ChainDataGeom.dot_nJ_vJ1_neg`, lives in a module
that is not upstream of `RegionSteps`; the caller discharges it with that lemma.
-/

set_option autoImplicit false

namespace Nivat.Colle35

open Nivat Nivat.LE2 Nivat.MaxEnv

variable {α : Type*}

/-- **The shell is a half-plane cut of one fixed swept set** (`shell_eq_reach_inter`, read
through `shellInf_eq`).  Only the level `c_J − ε` moves with `ε`. -/
theorem ChainDataWithShell.shellInf_eq_reach_inter {η xper : Config α} {vl : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (c : ChainDataWithShell η xper vl S gen) (ε : ℕ) :
    c.toChainData.shellInf ε =
      reachSet (⋃ i, c.toChainData.Ahat i) c.vJ1 ∩ halfPlaneGE c.nJ (c.cJ - (ε : ℤ)) := by
  rw [c.shellInf_eq, shell_eq_reach_inter]
  rfl

/-- The swept set is the union of all the shells: `hreach` is the `ε → ∞` limit. -/
theorem ChainDataWithShell.reachSet_eq_iUnion_shellInf {η xper : Config α} {vl : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (c : ChainDataWithShell η xper vl S gen) :
    reachSet (⋃ i, c.toChainData.Ahat i) c.vJ1 = ⋃ ε : ℕ, c.toChainData.shellInf ε := by
  ext z
  simp only [Set.mem_iUnion]
  constructor
  · intro hz
    refine ⟨(c.cJ - dot c.nJ z).toNat, ?_⟩
    rw [c.shellInf_eq_reach_inter]
    refine ⟨hz, ?_⟩
    show c.cJ - (((c.cJ - dot c.nJ z).toNat : ℕ) : ℤ) ≤ dot c.nJ z
    have := Int.self_le_toNat (c.cJ - dot c.nJ z)
    omega
  · rintro ⟨ε, hε⟩
    rw [c.shellInf_eq_reach_inter] at hε
    exact hε.1

/-- **The side condition, and what it buys**: if the swept set `reachSet Â_∞ v_{J-1}` is
lattice-convex, then so is every shell, by one half-plane cut. -/
theorem ChainDataWithShell.isLatticeConvexRegion_shellInf_of_reach {η xper : Config α}
    {vl : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (c : ChainDataWithShell η xper vl S gen)
    (hreach : IsLatticeConvexRegion (reachSet (⋃ i, c.toChainData.Ahat i) c.vJ1)) (ε : ℕ) :
    IsLatticeConvexRegion (c.toChainData.shellInf ε) := by
  rw [c.shellInf_eq_reach_inter]
  exact isLatticeConvexRegion_inter_halfPlaneGE hreach _ _

/-- `hreach` strictly strengthens `hRconv`: the `ε = 0` shell is `Â_∞` (`shellInf_zero_eq`). -/
theorem ChainDataWithShell.hRconv_of_reach {η xper : Config α} {vl : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (c : ChainDataWithShell η xper vl S gen)
    (hreach : IsLatticeConvexRegion (reachSet (⋃ i, c.toChainData.Ahat i) c.vJ1)) :
    IsLatticeConvexRegion (⋃ i, c.toChainData.Ahat i) := by
  rw [← c.shellInf_zero_eq]
  exact c.isLatticeConvexRegion_shellInf_of_reach hreach 0

/-- **`IsRegion (Â_∞^{(ε)}) p v_J` for every `ε`, under `hreach`.**  Convexity is the cut
above; the two rays are `ShellRegion.lean`'s, unconditional. -/
theorem ChainDataGeom.isRegion_shellInf_of_reach {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (cg : ChainDataGeom η xper vl p S gen)
    (hreach : IsLatticeConvexRegion (reachSet (⋃ i, cg.toChainData.Ahat i) cg.vJ1)) (ε : ℕ) :
    Colle41.IsRegion (cg.toChainData.shellInf ε) p cg.vJ :=
  (cg.isRegion_shellInf_iff ε).mpr
    (cg.toChainDataWithShell.isLatticeConvexRegion_shellInf_of_reach hreach ε)

/-- Contrapositive, in the form the refutations use: one non-convex shell kills `hreach`. -/
theorem ChainDataWithShell.not_reach_of_not_isLatticeConvexRegion_shellInf {η xper : Config α}
    {vl : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (c : ChainDataWithShell η xper vl S gen)
    {ε : ℕ} (h : ¬ IsLatticeConvexRegion (c.toChainData.shellInf ε)) :
    ¬ IsLatticeConvexRegion (reachSet (⋃ i, c.toChainData.Ahat i) c.vJ1) :=
  fun hreach => h (c.isLatticeConvexRegion_shellInf_of_reach hreach ε)

/-! ## The `ℓ_{J-1}`-edge -/

/-- **The `ℓ_{J-1}`-edge of `Â_∞`, at set level** (`b3_colle2.txt:402, :498-506`): the finite
edge of `conv Â_∞` adjacent to the semi-infinite `ℓ_J`-edge, parallel to the sweep direction
`v = v_{ℓ_{J-1}}`, with at least two lattice points.  `A` is `Â_∞`, `nJ`/`cJ` the support data
of `ℓ_J`. -/
structure EdgeJ1Data (A : Set (ℤ × ℤ)) (v nJ : ℤ × ℤ) (cJ : ℤ) where
  /-- The `ℓ_J`-vertex of `Â_∞`: initial point of the semi-infinite `ℓ_J`-edge (`:506`). -/
  a₀ : ℤ × ℤ
  a₀_mem : a₀ ∈ A
  /-- It lies on `ℓ_J`. -/
  a₀_on : dot nJ a₀ = cJ
  /-- The second lattice point of the edge, one `v`-step back (`:402`: `|ϖ ∩ Â_∞| ≥ |w ∩ S_φ| ≥ 2`). -/
  prev_mem : a₀ - v ∈ A
  /-- The normal of the edge line `ℓ_{J-1}`, oriented into `Â_∞`. -/
  nJ1 : ℤ × ℤ
  dot_nJ1_v : dot nJ1 v = 0
  nJ1_ne : nJ1 ≠ 0
  /-- `ℓ_{J-1}` supports `Â_∞` at `a₀`. -/
  support : ∀ g ∈ A, dot nJ1 a₀ ≤ dot nJ1 g

/-! ## Real inner products with an integer normal -/

/-- `⟪n, q⟫` for an integer normal `n` and a real point `q`. -/
def ip (n : ℤ × ℤ) (q : ℝ × ℝ) : ℝ := (n.1 : ℝ) * q.1 + (n.2 : ℝ) * q.2

theorem ip_toReal (n z : ℤ × ℤ) : ip n (toReal z) = (dot n z : ℝ) := by
  simp [ip, dot, toReal]

theorem ip_add (n : ℤ × ℤ) (q q' : ℝ × ℝ) : ip n (q + q') = ip n q + ip n q' := by
  simp only [ip, Prod.fst_add, Prod.snd_add]; ring

theorem ip_smul (n : ℤ × ℤ) (a : ℝ) (q : ℝ × ℝ) : ip n (a • q) = a * ip n q := by
  simp only [ip, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem isLinearMap_ip (n : ℤ × ℤ) : IsLinearMap ℝ (ip n) :=
  ⟨ip_add n, fun a q => ip_smul n a q⟩

theorem continuous_ip (n : ℤ × ℤ) : Continuous (ip n) := by
  unfold ip; fun_prop

/-- Cramer's rule, uniqueness half: two independent inner products determine a point of `ℝ²`. -/
theorem eq_of_ip_eq {n m : ℤ × ℤ} (hD : n.1 * m.2 - n.2 * m.1 ≠ 0) {q q' : ℝ × ℝ}
    (h1 : ip n q = ip n q') (h2 : ip m q = ip m q') : q = q' := by
  have hD' : ((n.1 : ℝ) * m.2 - n.2 * m.1) ≠ 0 := by exact_mod_cast hD
  simp only [ip] at h1 h2
  refine Prod.ext ?_ ?_
  · have h : ((n.1 : ℝ) * m.2 - n.2 * m.1) * (q.1 - q'.1) = 0 := by
      linear_combination (m.2 : ℝ) * h1 - (n.2 : ℝ) * h2
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hD'
    · linarith
  · have h : ((n.1 : ℝ) * m.2 - n.2 * m.1) * (q.2 - q'.2) = 0 := by
      linear_combination (n.1 : ℝ) * h2 - (m.1 : ℝ) * h1
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hD'
    · linarith

/-- Integer Cramer, uniqueness half: `y = 0` if both independent inner products vanish. -/
theorem eq_zero_of_dot_eq_zero {n m y : ℤ × ℤ} (hD : n.1 * m.2 - n.2 * m.1 ≠ 0)
    (h1 : dot n y = 0) (h2 : dot m y = 0) : y = 0 := by
  have e1 : (n.1 * m.2 - n.2 * m.1) * y.1 = dot n y * m.2 - dot m y * n.2 := by
    simp only [dot]; ring
  have e2 : (n.1 * m.2 - n.2 * m.1) * y.2 = dot m y * n.1 - dot n y * m.1 := by
    simp only [dot]; ring
  rw [h1, h2] at e1 e2
  simp only [zero_mul, sub_zero] at e1 e2
  rcases mul_eq_zero.mp e1 with h | h
  · exact absurd h hD
  · rcases mul_eq_zero.mp e2 with h' | h'
    · exact absurd h' hD
    · exact Prod.ext h h'

/-- Two normals are independent as soon as some vector is orthogonal to one and not the other. -/
theorem det_ne_zero_of_dot {n m v : ℤ × ℤ} (hnv : dot n v ≠ 0) (hmv : dot m v = 0)
    (hm : m ≠ 0) : n.1 * m.2 - n.2 * m.1 ≠ 0 := by
  intro hD
  apply hm
  have e1 : dot n v * m.2 = (n.1 * m.2 - n.2 * m.1) * v.1 + dot m v * n.2 := by
    simp only [dot]; ring
  have e2 : dot n v * m.1 = dot m v * n.1 - (n.1 * m.2 - n.2 * m.1) * v.2 := by
    simp only [dot]; ring
  rw [hD, hmv] at e1 e2
  simp only [zero_mul, zero_add, zero_sub, neg_zero] at e1 e2
  exact Prod.ext ((mul_eq_zero.mp e2).resolve_left hnv) ((mul_eq_zero.mp e1).resolve_left hnv)

/-! ## Hull facts -/

/-- A lattice half-plane bound on `A` passes to the closed convex hull. -/
theorem le_ip_of_mem_convHullOf {A : Set (ℤ × ℤ)} {n : ℤ × ℤ} {c : ℤ}
    (h : ∀ g ∈ A, c ≤ dot n g) {q : ℝ × ℝ} (hq : q ∈ convHullOf A) : (c : ℝ) ≤ ip n q := by
  have hsub : toReal '' A ⊆ {q : ℝ × ℝ | (c : ℝ) ≤ ip n q} := by
    rintro _ ⟨z, hz, rfl⟩
    show (c : ℝ) ≤ ip n (toReal z)
    rw [ip_toReal]; exact_mod_cast h z hz
  have hcl : IsClosed {q : ℝ × ℝ | (c : ℝ) ≤ ip n q} :=
    isClosed_le continuous_const (continuous_ip n)
  exact closure_minimal (convexHull_min hsub (convex_halfSpace_ge (isLinearMap_ip n) _)) hcl hq

/-- Real nonnegative multiples along a lattice ray land in the hull
(a copy of `ColleReg.real_ray_mem_convHullOf`, which is downstream of `RegionSteps`). -/
theorem real_ray_mem_convHullOf' {A : Set (ℤ × ℤ)} (hA : IsLatticeConvexRegion A)
    {z₀ d : ℤ × ℤ} (hray : ∀ k : ℕ, z₀ + (k : ℤ) • d ∈ A) {a : ℝ} (ha : 0 ≤ a) :
    toReal z₀ + a • toReal d ∈ convHullOf A := by
  have hmem : ∀ k : ℕ, toReal (z₀ + (k : ℤ) • d) ∈ convHullOf A := fun k => by
    have := hray k
    rw [eq_preimage_convHullOf hA] at this
    exact this
  set n := ⌊a⌋₊ with hn
  set r := a - (n : ℝ) with hr
  have hr0 : 0 ≤ r := by rw [hr]; linarith [Nat.floor_le ha]
  have hr1 : r ≤ 1 := by
    rw [hr]
    have := Nat.lt_floor_add_one a
    rw [← hn] at this
    linarith
  have hconv := (Nivat.convex_convHullOf A) (hmem n) (hmem (n + 1))
    (by linarith : (0 : ℝ) ≤ 1 - r) hr0 (by ring)
  have heq : (1 - r) • toReal (z₀ + (n : ℤ) • d) + r • toReal (z₀ + ((n + 1 : ℕ) : ℤ) • d)
      = toReal z₀ + a • toReal d := by
    apply Prod.ext <;>
      simp only [toReal, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
        smul_eq_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_add, Nat.cast_one] <;>
      push_cast <;> nlinarith [hr]
  rwa [heq] at hconv

/-! ## The band lemma -/

section Edge

variable {A : Set (ℤ × ℤ)} {v nJ vJ : ℤ × ℤ} {cJ : ℤ} (e : EdgeJ1Data A v nJ cJ)
  (hA : IsLatticeConvexRegion A)
  (hrec : ∀ g ∈ A, g + vJ ∈ A)
  (hnJvJ : dot nJ vJ = 0) (hnJv : dot nJ v < 0) (hvJ : vJ ≠ 0)

include e hnJv in
theorem EdgeJ1Data.det_ne_zero : nJ.1 * e.nJ1.2 - nJ.2 * e.nJ1.1 ≠ 0 :=
  det_ne_zero_of_dot (ne_of_lt hnJv) e.dot_nJ1_v e.nJ1_ne

include e hnJvJ hnJv hvJ in
theorem EdgeJ1Data.dot_nJ1_vJ_ne : dot e.nJ1 vJ ≠ 0 := by
  intro h
  exact hvJ (eq_zero_of_dot_eq_zero (e.det_ne_zero hnJv) hnJvJ h)

include e hrec hnJvJ hnJv hvJ in
theorem EdgeJ1Data.dot_nJ1_vJ_pos : 0 < dot e.nJ1 vJ := by
  have h := e.support _ (hrec _ e.a₀_mem)
  rw [dot_add] at h
  exact lt_of_le_of_ne (by linarith) (e.dot_nJ1_vJ_ne hnJvJ hnJv hvJ).symm

include e hA hrec hnJvJ hnJv hvJ in
/-- **The band lemma.**  A real point at level `[c_J, c_J − ⟪n_J, v⟫]` (one sweep step above
`ℓ_J`) and on the `Â_∞` side of `ℓ_{J-1}` lies in `conv Â_∞`: it is a convex combination of
points on the two lattice rays `a₀ + ℝ₊ v_J` and `(a₀ − v) + ℝ₊ v_J`. -/
theorem EdgeJ1Data.mem_convHullOf_of_band {q : ℝ × ℝ}
    (h1 : (cJ : ℝ) ≤ ip nJ q) (h2 : ip nJ q ≤ (cJ : ℝ) - (dot nJ v : ℝ))
    (h3 : (dot e.nJ1 e.a₀ : ℝ) ≤ ip e.nJ1 q) : q ∈ convHullOf A := by
  have hs : (0 : ℝ) < -(dot nJ v : ℝ) := by
    have : (dot nJ v : ℝ) < 0 := by exact_mod_cast hnJv
    linarith
  have hw : (0 : ℝ) < (dot e.nJ1 vJ : ℝ) := by
    exact_mod_cast e.dot_nJ1_vJ_pos hrec hnJvJ hnJv hvJ
  have hsne : (dot nJ v : ℝ) ≠ 0 := by
    have : (dot nJ v : ℝ) < 0 := by exact_mod_cast hnJv
    exact ne_of_lt this
  have hwne : (dot e.nJ1 vJ : ℝ) ≠ 0 := ne_of_gt hw
  set lam : ℝ := (ip nJ q - cJ) / (-(dot nJ v : ℝ)) with hlam
  set mu : ℝ := (ip e.nJ1 q - dot e.nJ1 e.a₀) / (dot e.nJ1 vJ : ℝ) with hmu
  have hlam0 : 0 ≤ lam := div_nonneg (by linarith) hs.le
  have hlam1 : lam ≤ 1 := by
    rw [hlam, div_le_one hs]; linarith
  have hmu0 : 0 ≤ mu := div_nonneg (by linarith) hw.le
  have hP₁ : toReal e.a₀ + mu • toReal vJ ∈ convHullOf A :=
    real_ray_mem_convHullOf' hA (fun k => Nivat.ColleReg.ray_of_recession hrec e.a₀_mem k) hmu0
  have hP₂ : toReal (e.a₀ - v) + mu • toReal vJ ∈ convHullOf A :=
    real_ray_mem_convHullOf' hA (fun k => Nivat.ColleReg.ray_of_recession hrec e.prev_mem k) hmu0
  have hcomb := (Nivat.convex_convHullOf A) hP₁ hP₂ (by linarith : (0 : ℝ) ≤ 1 - lam) hlam0
    (by ring)
  have heq : (1 - lam) • (toReal e.a₀ + mu • toReal vJ)
      + lam • (toReal (e.a₀ - v) + mu • toReal vJ) = q := by
    refine eq_of_ip_eq (e.det_ne_zero hnJv) ?_ ?_
    · simp only [ip_add, ip_smul, ip_toReal, dot_sub, e.a₀_on, hnJvJ]
      push_cast
      rw [hlam]
      field_simp [hsne]
      ring
    · simp only [ip_add, ip_smul, ip_toReal, dot_sub, e.dot_nJ1_v]
      push_cast
      rw [hmu]
      field_simp [hwne]
      ring
  rwa [heq] at hcomb

include e hA hrec hnJvJ hnJv hvJ in
/-- The lattice form of the band lemma. -/
theorem EdgeJ1Data.mem_of_band {g : ℤ × ℤ}
    (h1 : cJ ≤ dot nJ g) (h2 : dot nJ g ≤ cJ - dot nJ v)
    (h3 : dot e.nJ1 e.a₀ ≤ dot e.nJ1 g) : g ∈ A := by
  rw [eq_preimage_convHullOf hA]
  refine e.mem_convHullOf_of_band hA hrec hnJvJ hnJv hvJ ?_ ?_ ?_ <;>
    rw [ip_toReal] <;> exact_mod_cast ‹_›

end Edge

/-! ## Gluing two convex sets along a hyperplane -/

/-- **Gluing lemma.**  `C` lies on the side `f ≥ c` and `W` on the side `f ≤ c` of a
hyperplane; both sit inside a convex `E`; and every point of `E` *on* the hyperplane lies in
both.  Then `C ∪ W` is convex.  (The segment from `x ∈ C` to `y ∈ W` crosses the hyperplane at
a point of `E`, hence of `C ∩ W`, and each half of the segment lies in `C` resp. `W`.) -/
theorem convex_union_of_glue {C W E : Set (ℝ × ℝ)} (hC : Convex ℝ C) (hW : Convex ℝ W)
    (hE : Convex ℝ E) (hCE : C ⊆ E) (hWE : W ⊆ E) {f : ℝ × ℝ → ℝ} (hf : IsLinearMap ℝ f)
    {c : ℝ} (hCf : ∀ q ∈ C, c ≤ f q) (hWf : ∀ q ∈ W, f q ≤ c)
    (hglue : ∀ q ∈ E, f q = c → q ∈ C ∧ q ∈ W) : Convex ℝ (C ∪ W) := by
  -- the mixed case, `x ∈ C`, `y ∈ W`
  have mixed : ∀ x ∈ C, ∀ y ∈ W, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      a • x + b • y ∈ C ∪ W := by
    intro x hx y hy a b ha hb hab
    set u : ℝ := f x - c with hu
    set w : ℝ := c - f y with hw
    have hu0 : 0 ≤ u := by rw [hu]; linarith [hCf x hx]
    have hw0 : 0 ≤ w := by rw [hw]; linarith [hWf y hy]
    by_cases huw : u + w = 0
    · -- both endpoints on the hyperplane: `x ∈ W` too
      have hu' : u = 0 := by linarith
      have hxW : x ∈ W := (hglue x (hCE hx) (by rw [hu] at hu'; linarith)).2
      exact Or.inr (hW hxW hy ha hb hab)
    have huw' : 0 < u + w := lt_of_le_of_ne (by linarith) (Ne.symm huw)
    -- the crossing point
    set y' : ℝ × ℝ := (w / (u + w)) • x + (u / (u + w)) • y with hy'
    have hy'E : y' ∈ E := by
      refine hE (hCE hx) (hWE hy) (div_nonneg hw0 huw'.le) (div_nonneg hu0 huw'.le) ?_
      rw [← add_div, add_comm, div_self (ne_of_gt huw')]
    have hfy' : f y' = c := by
      rw [hy', hf.map_add, hf.map_smul, hf.map_smul]
      have hfx : f x = c + u := by rw [hu]; ring
      have hfy : f y = c - w := by rw [hw]; ring
      rw [hfx, hfy]
      simp only [smul_eq_mul]
      field_simp
      ring
    obtain ⟨hy'C, hy'W⟩ := hglue y' hy'E hfy'
    rcases le_or_gt (b * w) (a * u) with hle | hlt
    · -- the point is on the `C` side: between `x` and `y'`
      by_cases hu' : u = 0
      · have hbw : b * w = 0 := le_antisymm (by rw [hu'] at hle; linarith) (mul_nonneg hb hw0)
        rcases mul_eq_zero.mp hbw with hb0 | hw0'
        · have ha1 : a = 1 := by linarith
          rw [hb0, ha1, one_smul, zero_smul, add_zero]
          exact Or.inl hx
        · exact absurd (by rw [hu', hw0']; ring : u + w = 0) huw
      have hupos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu')
      refine Or.inl ?_
      have hkey : a • x + b • y = ((a * u - b * w) / u) • x + (b * (u + w) / u) • y' := by
        rw [hy', smul_add, smul_smul, smul_smul]
        refine Prod.ext ?_ ?_ <;>
          simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
          field_simp <;> ring
      rw [hkey]
      refine hC hx hy'C (div_nonneg (by linarith) hupos.le)
        (div_nonneg (mul_nonneg hb huw'.le) hupos.le) ?_
      rw [← add_div, div_eq_one_iff_eq (ne_of_gt hupos)]
      linear_combination u * hab
    · -- the point is on the `W` side: between `y'` and `y`
      have hwpos : 0 < w := by
        rcases lt_or_eq_of_le hw0 with h | h
        · exact h
        · exfalso; rw [← h, mul_zero] at hlt; linarith [mul_nonneg ha hu0]
      refine Or.inr ?_
      have hkey : a • x + b • y = (a * (u + w) / w) • y' + ((b * w - a * u) / w) • y := by
        rw [hy', smul_add, smul_smul, smul_smul]
        refine Prod.ext ?_ ?_ <;>
          simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
          field_simp <;> ring
      rw [hkey]
      refine hW hy'W hy (div_nonneg (mul_nonneg ha huw'.le) hwpos.le)
        (div_nonneg (by linarith) hwpos.le) ?_
      rw [← add_div, div_eq_one_iff_eq (ne_of_gt hwpos)]
      linear_combination w * hab
  intro x hx y hy a b ha hb hab
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Or.inl (hC hx hy ha hb hab)
  · exact mixed x hx y hy a b ha hb hab
  · rw [add_comm]
    exact mixed y hy x hx b a hb ha (by linarith)
  · exact Or.inr (hW hx hy ha hb hab)

/-! ## The main theorem -/

private theorem dot_zsmul' (n : ℤ × ℤ) (k : ℤ) (w : ℤ × ℤ) : dot n (k • w) = k * dot n w := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

section Main

variable {A : Set (ℤ × ℤ)} {v nJ vJ : ℤ × ℤ} {cJ : ℤ} (e : EdgeJ1Data A v nJ cJ)
  (hA : IsLatticeConvexRegion A)
  (hAhalf : ∀ g ∈ A, cJ ≤ dot nJ g)
  (hzero : reachSet A v ∩ halfPlaneGE nJ cJ ⊆ A)
  (hrec : ∀ g ∈ A, g + vJ ∈ A)
  (hnJvJ : dot nJ vJ = 0) (hnJv : dot nJ v < 0) (hvJ : vJ ≠ 0)

include e hA hAhalf hzero hrec hnJvJ hnJv hvJ in
/-- **`edge ⇒ hreach`.**  With an `ℓ_{J-1}`-edge, the swept set `reachSet Â_∞ v_{J-1}` is a
lattice-convex region, for **any** sweep step `⟪n_J, v⟫ < 0`.  The certificate is
`conv Â_∞ ∪ {⟪n_J,·⟫ ≤ c_J, ⟪n_{J-1},·⟫ ≥ ⟪n_{J-1}, a₀⟫}`, glued along `ℓ_J`
(`convex_union_of_glue`); the lattice points of the wedge are reached because the band lemma
puts every lattice point at level `[c_J, c_J + |⟪n_J, v⟫|)` into `Â_∞`.

Hypotheses in bundle terms: `hA = hRconv`, `hAhalf = ahat_halfPlane`,
`hzero = shellInfZero` (through `shellInf_eq_reach_inter` at `ε = 0`), `hrec = rec_vJ`,
`hnJvJ = dot_nJ_vJ`, `hnJv = ANormal.ChainDataGeom.dot_nJ_vJ1_neg`, `hvJ = vJ_ne`. -/
theorem EdgeJ1Data.isLatticeConvexRegion_reachSet : IsLatticeConvexRegion (reachSet A v) := by
  set c₁ : ℤ := dot e.nJ1 e.a₀ with hc₁
  set C : Set (ℝ × ℝ) := convHullOf A with hC
  set W : Set (ℝ × ℝ) := {q | ip nJ q ≤ cJ ∧ (c₁ : ℝ) ≤ ip e.nJ1 q} with hW
  set E : Set (ℝ × ℝ) := {q | (c₁ : ℝ) ≤ ip e.nJ1 q} with hE
  have hCE : C ⊆ E := fun q hq => le_ip_of_mem_convHullOf e.support hq
  refine ⟨C ∪ W, ?_, ?_, ?_⟩
  · -- convex
    refine convex_union_of_glue (Nivat.convex_convHullOf A) ?_ ?_ hCE (fun q hq => hq.2)
      (isLinearMap_ip nJ) (c := (cJ : ℝ)) (fun q hq => le_ip_of_mem_convHullOf hAhalf hq)
      (fun q hq => hq.1) ?_
    · exact (convex_halfSpace_le (isLinearMap_ip nJ) _).inter
        (convex_halfSpace_ge (isLinearMap_ip e.nJ1) _)
    · exact convex_halfSpace_ge (isLinearMap_ip e.nJ1) _
    · intro q hq hfq
      refine ⟨e.mem_convHullOf_of_band hA hrec hnJvJ hnJv hvJ hfq.ge ?_ hq, hfq.le, hq⟩
      have : (dot nJ v : ℝ) < 0 := by exact_mod_cast hnJv
      linarith
  · -- closed
    exact (Nivat.isClosed_convHullOf A).union
      ((isClosed_le (continuous_ip nJ) continuous_const).inter
        (isClosed_le continuous_const (continuous_ip e.nJ1)))
  · -- the lattice points
    ext z
    constructor
    · rintro ⟨g, hg, t, rfl⟩
      by_cases h : cJ ≤ dot nJ (g + (t : ℤ) • v)
      · exact Or.inl (Nivat.mem_convHullOf_of_mem (hzero ⟨⟨g, hg, t, rfl⟩, h⟩))
      · refine Or.inr ⟨?_, ?_⟩
        · show ip nJ (toReal (g + (t : ℤ) • v)) ≤ cJ
          rw [ip_toReal]; exact_mod_cast (not_le.mp h).le
        · show (c₁ : ℝ) ≤ ip e.nJ1 (toReal (g + (t : ℤ) • v))
          rw [ip_toReal, dot_add, dot_zsmul', e.dot_nJ1_v, mul_zero, add_zero]
          exact_mod_cast e.support g hg
    · rintro (h | ⟨h1, h2⟩)
      · have hzA : z ∈ A := by rw [eq_preimage_convHullOf hA]; exact h
        exact ⟨z, hzA, 0, by simp⟩
      · change ip nJ (toReal z) ≤ cJ at h1
        change (c₁ : ℝ) ≤ ip e.nJ1 (toReal z) at h2
        rw [ip_toReal] at h1 h2
        have h1' : dot nJ z ≤ cJ := by exact_mod_cast h1
        have h2' : c₁ ≤ dot e.nJ1 z := by exact_mod_cast h2
        -- the sweep index: the least `t` with `c_J ≤ ⟪n_J, z − t v⟫`
        set s : ℤ := -dot nJ v with hs
        have hs0 : 0 < s := by rw [hs]; linarith
        set d : ℤ := cJ - dot nJ z with hd
        have hd0 : 0 ≤ d := by rw [hd]; linarith
        set q : ℤ := (d + s - 1) / s with hq
        have hdiv := Int.mul_ediv_add_emod (d + s - 1) s
        have hmod0 := Int.emod_nonneg (d + s - 1) (ne_of_gt hs0)
        have hmodlt := Int.emod_lt_of_pos (d + s - 1) hs0
        have hq1 : d ≤ s * q := by rw [hq]; linarith
        have hq2 : s * q ≤ d + s - 1 := by rw [hq]; linarith
        have hq0 : 0 ≤ q := Int.ediv_nonneg (by linarith) hs0.le
        have hqv : q * dot nJ v = -(s * q) := by rw [hs]; ring
        refine ⟨z - q • v, ?_, q.toNat, ?_⟩
        · refine e.mem_of_band hA hrec hnJvJ hnJv hvJ ?_ ?_ ?_
          · rw [dot_sub, dot_zsmul', hqv]; linarith
          · rw [dot_sub, dot_zsmul', hqv]; linarith
          · rw [dot_sub, dot_zsmul', e.dot_nJ1_v, mul_zero, sub_zero]; exact h2'
        · rw [Int.toNat_of_nonneg hq0]; abel

end Main

/-! ## Bundle wrappers -/

/-- The `ℓ_{J-1}`-edge of a chain's `Â_∞`, read off the bundle's `v_{J-1}`, `n_J`, `c_J`. -/
abbrev ChainDataWithShell.EdgeJ1 {η xper : Config α} {vl : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    {gen : ℤ × ℤ} (c : ChainDataWithShell η xper vl S gen) : Type :=
  EdgeJ1Data (⋃ i, c.toChainData.Ahat i) c.vJ1 c.nJ c.cJ

/-- `hzero` in bundle terms: `shellInfZero` through `shellInf_eq_reach_inter` at `ε = 0`. -/
theorem ChainDataWithShell.reachSet_inter_halfPlaneGE_subset {η xper : Config α} {vl : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (c : ChainDataWithShell η xper vl S gen) :
    reachSet (⋃ i, c.toChainData.Ahat i) c.vJ1 ∩ halfPlaneGE c.nJ c.cJ ⊆
      ⋃ i, c.toChainData.Ahat i := by
  have h := c.shellInfZero
  rw [c.shellInf_eq_reach_inter 0] at h
  simpa using h

/-- **`edge ⇒ hreach`, on the bundle.**  `hnJv` is `ANormal.ChainDataGeom.dot_nJ_vJ1_neg`,
taken as a binder because `ANormal.lean` is not upstream of `RegionSteps.lean`. -/
theorem ChainDataGeom.hreach_of_edgeJ1 {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (cg : ChainDataGeom η xper vl p S gen)
    (e : cg.toChainDataWithShell.EdgeJ1)
    (hRconv : IsLatticeConvexRegion (⋃ i, cg.toChainData.Ahat i))
    (hnJv : dot cg.nJ cg.vJ1 < 0) :
    IsLatticeConvexRegion (reachSet (⋃ i, cg.toChainData.Ahat i) cg.vJ1) :=
  e.isLatticeConvexRegion_reachSet hRconv cg.ahat_halfPlane
    cg.toChainDataWithShell.reachSet_inter_halfPlaneGE_subset cg.rec_vJ cg.dot_nJ_vJ hnJv cg.vJ_ne

/-- **`IsRegion (Â_∞^{(ε)}) p v_J` for every `ε`, given the `ℓ_{J-1}`-edge.**  This is the
conjunct `Colle41.IsRegion R p cg.vJ` of `exists_case2_window` at `R := shellInf ε`. -/
theorem ChainDataGeom.isRegion_shellInf_of_edgeJ1 {η xper : Config α} {vl p : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} (cg : ChainDataGeom η xper vl p S gen)
    (e : cg.toChainDataWithShell.EdgeJ1)
    (hRconv : IsLatticeConvexRegion (⋃ i, cg.toChainData.Ahat i))
    (hnJv : dot cg.nJ cg.vJ1 < 0) (ε : ℕ) :
    Colle41.IsRegion (cg.toChainData.shellInf ε) p cg.vJ :=
  cg.isRegion_shellInf_of_reach (cg.hreach_of_edgeJ1 e hRconv hnJv) ε

end Nivat.Colle35

#print axioms Nivat.Colle35.ChainDataWithShell.shellInf_eq_reach_inter
#print axioms Nivat.Colle35.ChainDataWithShell.reachSet_eq_iUnion_shellInf
#print axioms Nivat.Colle35.ChainDataWithShell.isLatticeConvexRegion_shellInf_of_reach
#print axioms Nivat.Colle35.ChainDataWithShell.hRconv_of_reach
#print axioms Nivat.Colle35.ChainDataGeom.isRegion_shellInf_of_reach
#print axioms Nivat.Colle35.ChainDataWithShell.not_reach_of_not_isLatticeConvexRegion_shellInf
#print axioms Nivat.Colle35.EdgeJ1Data.mem_of_band
#print axioms Nivat.Colle35.convex_union_of_glue
#print axioms Nivat.Colle35.EdgeJ1Data.isLatticeConvexRegion_reachSet
#print axioms Nivat.Colle35.ChainDataWithShell.reachSet_inter_halfPlaneGE_subset
#print axioms Nivat.Colle35.ChainDataGeom.hreach_of_edgeJ1
#print axioms Nivat.Colle35.ChainDataGeom.isRegion_shellInf_of_edgeJ1
