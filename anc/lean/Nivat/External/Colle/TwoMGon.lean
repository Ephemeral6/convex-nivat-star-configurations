/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: lane-hroom-close
-/
import Nivat.External.Colle.RegionEdges
import Nivat.External.Colle.ShellSweep

/-!
# Generalizing the "cone collapse" trick beyond `m = 3`

`shellEnv` (`ChainData.shellEnv`, produced only by `exists_chainData` in `RegionSteps.lean`,
still `sorry`) is required to hold for **general** `DecompData.m` (only `hm : 2 ≤ m`, never
pinned to `3` on chain — confirmed independently by `lane-chaindata-lead` and the integrator,
`LANDING.md` Round 80). `ShellSweep.lean`'s `hexShape`/`E_hexShape`/`enveloped_hexShape` are
an `m = 3`-scoped worked instance (six explicit normals `±(1,0), ±(0,1), ±(1,-1)`) and do not
generalize by substitution; the real deliverable is a `2m`-gon analogue.

The `⊆` direction of `E_hexShape` (`face_subsingleton_hexShape`, `ShellSweep.lean`) is proved
by hardcoded case-splits on the sign of the two coordinates plus `x - y`, each closed by
`face_subset_singleton_of_cone` (`ShellSweep.lean:73`). That lemma takes integer cone
coefficients `α, β` **supplied by hand** — for `hexShape` they happen to always be `1`, because
every pair of consecutive edge normals there has `det = 1`. For a general `2m`-gon, consecutive
edge normals need not be unimodular (`det m₁ m₂` can be any positive integer), so a literal
substitution of `face_subset_singleton_of_cone` does not typecheck for a hand-picked `α, β`.

This file removes that obstruction: `face_subset_singleton_of_between` replaces the
hand-supplied `⟨α, β⟩` with the **Cramer decomposition** of `n` in the `(m₁, m₂)` basis, scaled
by `det m₁ m₂` to stay in `ℤ`. The hypothesis becomes exactly "`n` is strictly inside the cone
spanned by `m₁, m₂`" as a `det`-sign condition — the same vocabulary `RegionEdges.lean`'s
`cycBtw_of_cone` already uses to phrase "strictly between in cyclic order" — with **no
integrality side condition** on the consecutive edge normals. This is the reusable primitive a
`2m`-gon version of `E_hexShape`'s `⊆` direction needs at each of its `2m` bracket cases,
in place of `hexShape`'s six hand-picked-coefficient case splits.

## Status

`cramer_dot`, `face_subset_singleton_of_cone'`, `face_subset_singleton_of_between`: all 0
sorry. Pure linear algebra over `ℤ × ℤ`; no chain object referenced yet. Consumer: the still
unwritten `2m`-gon analogue of `E_hexShape`'s `⊆` direction (not this file — that needs the
cyclic normal-fan data `N : Fin (2*m) → ℤ × ℤ` plus a "locate the bracketing pair" lemma built
from `RegionEdges.lean`'s `angLT_iff_det` / `cycBtw_of_cone` / `half_eq_of_cone`, still to be
written). Reported to `lane-chaindata-lead` for the scope check before further build-out.
-/

set_option autoImplicit false

namespace Nivat.TwoMGon

open Nivat Nivat.LE2

/-- **Cramer's identity**, scaled to stay in `ℤ`: for any `n, m₁, m₂ ∈ ℤ × ℤ`,
`det m₁ m₂ • n = det n m₂ • m₁ + det m₁ n • m₂` as linear functionals (paired against any `z`).
No hypothesis needed — this is a polynomial identity in the six coordinates.

Dedup (team-lead, Round 88 follow-up): this is `RegionEdges.lean:69`'s `cramer_dot n n' m z`
under the argument permutation `(n, n', m) ↦ (m₁, m₂, n)` — reused directly rather than
re-proved. -/
theorem cramer_dot (n m₁ m₂ z : ℤ × ℤ) :
    det m₁ m₂ * dot n z = det n m₂ * dot m₁ z + det m₁ n * dot m₂ z :=
  Nivat.LE2.cramer_dot m₁ m₂ n z

/-- **A face in the (possibly non-unimodular) cone of two adjacent constraint normals is a
single vertex**, with the cone coefficients supplied pre-scaled by `D` rather than assumed
integral on their own. This is `ShellSweep.face_subset_singleton_of_cone` with the
`hn`/coefficient hypothesis generalized from `dot n z = α dot m₁ z + β dot m₂ z` to
`D * dot n z = α dot m₁ z + β dot m₂ z`, `D > 0` — the proof is identical, just scaled
throughout by `D` before comparing. -/
theorem face_subset_singleton_of_cone' {R : Set (ℤ × ℤ)} {n m₁ m₂ v : ℤ × ℤ} {D α β c₁ c₂ : ℤ}
    (hD : 0 < D) (hα : 0 < α) (hβ : 0 < β)
    (hn : ∀ z, D * dot n z = α * dot m₁ z + β * dot m₂ z) (hDet : det m₁ m₂ ≠ 0)
    (h₁ : ∀ z ∈ R, dot m₁ z ≤ c₁) (h₂ : ∀ z ∈ R, dot m₂ z ≤ c₂)
    (hv : v ∈ R) (hv₁ : dot m₁ v = c₁) (hv₂ : dot m₂ v = c₂) :
    face R n ⊆ {v} := by
  intro z hz
  have hle : dot n v ≤ dot n z := hz.2 v hv
  have hleD : D * dot n v ≤ D * dot n z := mul_le_mul_of_nonneg_left hle hD.le
  have hA : 0 ≤ α * (c₁ - dot m₁ z) := mul_nonneg hα.le (by linarith [h₁ z hz.1])
  have hB : 0 ≤ β * (c₂ - dot m₂ z) := mul_nonneg hβ.le (by linarith [h₂ z hz.1])
  have hsum : α * (c₁ - dot m₁ z) + β * (c₂ - dot m₂ z) ≤ 0 := by
    rw [hn v, hn z, hv₁, hv₂] at hleD; linarith
  have e₁ : dot m₁ z = c₁ := by
    have hz0 : α * (c₁ - dot m₁ z) = 0 := by linarith
    rcases mul_eq_zero.mp hz0 with h | h
    · exact absurd h hα.ne'
    · linarith
  have e₂ : dot m₂ z = c₂ := by
    have hz0 : β * (c₂ - dot m₂ z) = 0 := by linarith
    rcases mul_eq_zero.mp hz0 with h | h
    · exact absurd h hβ.ne'
    · linarith
  exact eq_of_dot_eq_dot hDet (e₁.trans hv₁.symm) (e₂.trans hv₂.symm)

/-- **The reusable "bracket" collapse lemma, in `det`-only vocabulary.** If `n` is strictly
inside the cone spanned by `m₁, m₂` (`det m₁ m₂ > 0`, i.e. `m₂` is counter-clockwise of `m₁`,
and `n` is strictly between them: `det n m₂ > 0`, `det m₁ n > 0` — exactly
`RegionEdges.cycBtw_of_cone`'s hypotheses), and both constraints are tight at a shared point
`v ∈ R`, then `face R n ⊆ {v}`. Unlike `ShellSweep.face_subset_singleton_of_cone`, no cone
coefficients need to be supplied or shown integral by hand: `cramer_dot` supplies them
automatically, for any `m₁, m₂`, unimodular or not. This is the primitive a `2m`-gon `⊆`
direction (`E (PolyShape N c) ⊆ Set.range N`, still to be written) applies once per bracket
case, taking `m₁ := N i`, `m₂ := N (i+1)`, `v := ` the shared vertex, replacing `hexShape`'s six
hand-picked-coefficient splits. -/
theorem face_subset_singleton_of_between {R : Set (ℤ × ℤ)} {n m₁ m₂ v : ℤ × ℤ} {c₁ c₂ : ℤ}
    (hD : 0 < det m₁ m₂) (hα : 0 < det n m₂) (hβ : 0 < det m₁ n)
    (h₁ : ∀ z ∈ R, dot m₁ z ≤ c₁) (h₂ : ∀ z ∈ R, dot m₂ z ≤ c₂)
    (hv : v ∈ R) (hv₁ : dot m₁ v = c₁) (hv₂ : dot m₂ v = c₂) :
    face R n ⊆ {v} :=
  face_subset_singleton_of_cone' hD hα hβ (fun z => cramer_dot n m₁ m₂ z) hD.ne'
    h₁ h₂ hv hv₁ hv₂

/-! ## Det-sign transfer across `CycBtw` (the "locate bracket" crux)

`RegionEdges.cycBtw_of_cone` proves cone-containment ⟹ `CycBtw`. The `2m`-gon `⊆` direction
needs the converse: given `w` cyclically between `u` and `v` (`CycBtw u w v`), and `u, v` a
"short arc" (`0 < det u v`), transfer that to `0 < det u w ∧ 0 < det w v`. Plain `angLT`-
betweenness is not enough by itself (`a := (1,0)`, `n := (0,-1)`: `angLT a n` holds since
`half a = 0 < half n = 1`, but `det a n = -1 < 0`) — the extra `0 < det u v` "short arc" context
is load-bearing. Same-half sub-cases close directly via `angSlope_lt_iff_det`; cross-half
sub-cases need `cramer_snd`/`cramer_fst`, mirroring `half_eq_of_cone`'s technique. -/

open Nivat.LE2 in
/-- Cross-half helper: `u` at half `0`, `v` at half `1`, `0 < det u v`, `w` also at half `0`
with `0 < det u w` already known (same-half, so free) ⟹ `0 < det w v`. -/
theorem det_pos_cross_of_half0 {u v w : ℤ × ℤ} (hD : 0 < det u v) (huw : 0 < det u w)
    (hu : 0 < u.2 ∨ (u.2 = 0 ∧ 0 < u.1)) (hv : v.2 < 0 ∨ (v.2 = 0 ∧ v.1 < 0))
    (hw : 0 < w.2 ∨ (w.2 = 0 ∧ 0 < w.1)) : 0 < det w v := by
  have hc := cramer_snd u v w
  have hc2 := cramer_fst u v w
  simp only [det] at hD huw hc hc2 ⊢
  rcases hu with hu | ⟨hu2, hu1⟩ <;> rcases hv with hv | ⟨hv2, hv1⟩ <;>
      rcases hw with hw | ⟨hw2, hw1⟩ <;>
    first
      | nlinarith [hc, hc2, hD, huw]
      | nlinarith [hc, hc2, hD, huw, mul_pos hu hw1, mul_eq_zero_of_right u.1 hw2]

open Nivat.LE2 in
/-- Mirror of `det_pos_cross_of_half0`: `w` at half `1` (same as `v`), `0 < det w v` free
⟹ `0 < det u w`. -/
theorem det_pos_cross_of_half1 {u v w : ℤ × ℤ} (hD : 0 < det u v) (hwv : 0 < det w v)
    (hu : 0 < u.2 ∨ (u.2 = 0 ∧ 0 < u.1)) (hv : v.2 < 0 ∨ (v.2 = 0 ∧ v.1 < 0))
    (hw : w.2 < 0 ∨ (w.2 = 0 ∧ w.1 < 0)) : 0 < det u w := by
  have hc := cramer_snd u v w
  have hc2 := cramer_fst u v w
  simp only [det] at hD hwv hc hc2 ⊢
  rcases hu with hu | ⟨hu2, hu1⟩ <;> rcases hv with hv | ⟨hv2, hv1⟩ <;>
      rcases hw with hw | ⟨hw2, hw1⟩ <;>
    first
      | nlinarith [hc, hc2, hD, hwv]
      | nlinarith [hc, hc2, hD, hwv, mul_neg_of_pos_of_neg hu1 hv, mul_eq_zero_of_left hu2 v.1]

open Nivat.LE2 in
/-- `det` is invariant under negating both arguments — lets the "wrap" configuration (`u` at
half `1`, `v` at half `0`, short arc crossing the `angLT` discontinuity) reduce to the two
lemmas above via `u ↦ -u, v ↦ -v, w ↦ -w` (negation flips every `half`, fixes `det`). -/
theorem det_neg_neg (a b : ℤ × ℤ) : det (-a) (-b) = det a b := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

open Nivat.LE2 in
/-- Bridging form of `half_eq_one_iff` with the direct (non-negated) disjunction on the RHS,
via `Int` trichotomy. Needs `a ≠ 0`: at `a = (0,0)`, `half a = 1` (the `else` branch) but the
direct disjunction is false (`a.2 = 0` and `a.1 = 0` is not `a.1 < 0`). -/
theorem half_eq_one_iff' {a : ℤ × ℤ} (ha : a ≠ 0) :
    half a = 1 ↔ (a.2 < 0 ∨ (a.2 = 0 ∧ a.1 < 0)) := by
  constructor
  · intro h
    have hne : ¬(0 < a.2 ∨ (a.2 = 0 ∧ 0 < a.1)) := half_eq_one_iff.mp h
    have hle : a.2 ≤ 0 := by by_contra hcon; exact hne (Or.inl (by omega))
    rcases eq_or_lt_of_le hle with he | hlt
    · right
      refine ⟨he, ?_⟩
      have ha1 : a.1 ≠ 0 := by
        intro h1
        exact ha (Prod.ext h1 he)
      by_contra hcon
      exact hne (Or.inr ⟨he, by omega⟩)
    · left; exact hlt
  · intro h
    rw [half_eq_one_iff]
    rintro (hc | ⟨hc1, hc2⟩) <;> omega

open Nivat.LE2 in
/-- **The crux "locate bracket" lemma.** `w` cyclically between `u` and `v`, with `u, v` a
short arc (`0 < det u v`), transfers to `w` genuinely lying in the `det`-cone between them.
Non-wrap case (`CycBtw`'s first disjunct): `half u ≤ half w ≤ half v` is forced by `angLT`, so
only the four monotone `half`-triples survive; same-half pairs close directly via
`angLT_iff_det`, cross-half pairs via `det_pos_cross_of_half0/1`. Wrap case (second disjunct):
`angLT v u` forces `half v < half u` (the `angLT u v` route is blocked by `hD`), landing in
`half u = 1, half v = 0`; reduced to the non-wrap helpers via `det_neg_neg`. -/
theorem det_pos_of_cycBtw_short {u w v : ℤ × ℤ} (hu : u ≠ 0) (hw : w ≠ 0) (hv : v ≠ 0)
    (hD : 0 < det u v) (hcyc : CycBtw u w v) : 0 < det u w ∧ 0 < det w v := by
  unfold CycBtw at hcyc
  rcases hcyc with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · -- non-wrap: angLT u v, angLT u w, angLT w v
    have e2 := (angLT_iff_det hu hw).mp h2
    have e3 := (angLT_iff_det hw hv).mp h3
    have hle_uw : half u ≤ half w := by rcases e2 with h | ⟨h, _⟩ <;> omega
    have hle_wv : half w ≤ half v := by rcases e3 with h | ⟨h, _⟩ <;> omega
    rcases half_cases u with pu0 | pu1 <;> rcases half_cases w with pw0 | pw1 <;>
        rcases half_cases v with pv0 | pv1
    · exact ⟨(e2.resolve_left (by omega)).2, (e3.resolve_left (by omega)).2⟩
    · have hduw : 0 < det u w := (e2.resolve_left (by omega)).2
      refine ⟨hduw, det_pos_cross_of_half0 hD hduw (half_eq_zero_iff.mp pu0)
        (half_eq_one_iff' hv |>.mp pv1) (half_eq_zero_iff.mp pw0)⟩
    · exfalso; omega
    · have hdwv : 0 < det w v := (e3.resolve_left (by omega)).2
      refine ⟨det_pos_cross_of_half1 hD hdwv (half_eq_zero_iff.mp pu0)
        (half_eq_one_iff' hv |>.mp pv1) (half_eq_one_iff' hw |>.mp pw1), hdwv⟩
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · exact ⟨(e2.resolve_left (by omega)).2, (e3.resolve_left (by omega)).2⟩
  · -- wrap: angLT v u, angLT u w ∨ angLT w v
    have huv0 : det v u < 0 := by
      have h : det v u = -det u v := by simp only [det]; ring
      linarith [h, hD]
    have e1 := (angLT_iff_det hv hu).mp h1
    have hlt : half v < half u := e1.resolve_right (by rintro ⟨-, hc⟩; omega)
    have hu1 : half u = 1 := by rcases half_cases u with h | h <;> omega
    have hv0 : half v = 0 := by rcases half_cases v with h | h <;> omega
    have hun := half_eq_one_iff' hu |>.mp hu1
    have hvn := half_eq_zero_iff.mp hv0
    have hDneg : 0 < det (-u) (-v) := by rw [det_neg_neg]; exact hD
    have hunneg : 0 < (-u).2 ∨ ((-u).2 = 0 ∧ 0 < (-u).1) := by
      simp only [Prod.fst_neg, Prod.snd_neg]; omega
    have hvnneg : (-v).2 < 0 ∨ ((-v).2 = 0 ∧ (-v).1 < 0) := by
      simp only [Prod.fst_neg, Prod.snd_neg]; omega
    rcases h2 with h2 | h2
    · have hwc := half_cases w
      have e2 := (angLT_iff_det hu hw).mp h2
      have hduw : 0 < det u w := (e2.resolve_left (by omega)).2
      have hw1 : half w = 1 := by
        rcases e2 with h | ⟨h, -⟩
        · omega
        · omega
      have hwn := half_eq_one_iff' hw |>.mp hw1
      have hwnneg : 0 < (-w).2 ∨ ((-w).2 = 0 ∧ 0 < (-w).1) := by
        simp only [Prod.fst_neg, Prod.snd_neg]; omega
      have huwneg : 0 < det (-u) (-w) := by rw [det_neg_neg]; exact hduw
      have hwvneg : 0 < det (-w) (-v) :=
        det_pos_cross_of_half0 hDneg huwneg hunneg hvnneg hwnneg
      rw [det_neg_neg] at hwvneg
      exact ⟨hduw, hwvneg⟩
    · have e3 := (angLT_iff_det hw hv).mp h2
      have hdwv : 0 < det w v := (e3.resolve_left (by omega)).2
      have hw0 : half w = 0 := by
        rcases e3 with h | ⟨h, -⟩
        · omega
        · omega
      have hwn := half_eq_zero_iff.mp hw0
      have hwnneg : (-w).2 < 0 ∨ ((-w).2 = 0 ∧ (-w).1 < 0) := by
        simp only [Prod.fst_neg, Prod.snd_neg]; omega
      have hwvneg : 0 < det (-w) (-v) := by rw [det_neg_neg]; exact hdwv
      have huwneg : 0 < det (-u) (-w) :=
        det_pos_cross_of_half1 hDneg hwvneg hunneg hvnneg hwnneg
      rw [det_neg_neg] at huwneg
      exact ⟨huwneg, hdwv⟩

/-! ## History (硬规矩 6): the superseded `k`-indexed struct

An earlier `k`-indexed `PolyFan` with bare `hccw : ∀ i, 0 < det (N i) (N (i+1))` and a hand-built
`hexFan6` (`hexShape 2 2 1 1 0`'s six normals) passed `decide` on every field, but
`lane-chaindata-lead`'s `badFan` (`tmp/wip/lane-cd-fanscope.lean`) kernel-checked a counterexample
where every `hccw` holds (`det = 1`) yet `N` winds twice (`Set.range N` has only 3 elements for
`k = 6`) — `hccw` alone does not force a single non-self-intersecting loop, with or without
antipodal symmetry (see the Round 91 redesign below). That struct and instance are removed here;
`hv_mem`, discovered missing in the same pass (`htight1`/`htight2` alone don't pin `v i` against
the other `k - 2` constraints), carries over unchanged into the redesign. -/

/-! ## Round 91 redesign: real underlying region, `hadj`/`E T` in place of bare `hccw`

Superseded design (team-lead ruling, `LANDING.md` Round 91): the `k`-indexed `PolyFan` above
with bare `hccw` admits `lane-cd-fanscope.lean`'s `badFan` double-winding counterexample, and
`hccw` + antipodal symmetry alone still doesn't give the "no other edge normal sits strictly
between consecutive fan normals" fact the bracket lemma actually needs — that fact is exactly
what the established `hadj`-idiom already used by `PolyChain.adjacent_shared_vertex`
(`PolyChain.lean:245-248`) and `FanEndpoint.mem_face_of_adjacent_endpoint_ccw/cw`
(`FanEndpoint.lean:81-200`) hands in as a hypothesis rather than derives from `det`-positivity
alone. So: carry the real region `T`, `hlc : IsLatticeConvexRegion T`, and `hEeq : E T =
Set.range N` as fields (the genuinely hard geometric content — `E T` has exactly `2m` elements,
no more no fewer — deferred to whoever instantiates `PolyFan` against real geometric data, not
proved generically here), index by `Fin (2*m)` with `hanti : N (i + m) = -N i` (textual
counterpart: `b3_colle2.txt:424,541,764`, `2m` edges + antipodal structure), and replace `hccw`
by the per-`i` `hadj` guard. -/

open Nivat.Colle41 in
/-- `IsLatticeConvexRegion` is preserved by any **finite intersection of half-planes** — the
generic base case a `PolyFan`'s `hlc` field reduces to for any concrete `N, c`. Induction on the
index type `Fin n`, peeling off the last constraint via `isLatticeConvexRegion_inter_halfPlaneLE`
(`RegionEdges.lean:656`), bottoming out at `isLatticeConvexRegion_univ` (`Lemma41.lean:745`). -/
theorem isLatticeConvexRegion_iInter_halfPlaneLE :
    ∀ (n : ℕ) (N : Fin n → ℤ × ℤ) (c : Fin n → ℤ),
      IsLatticeConvexRegion {z : ℤ × ℤ | ∀ i, dot (N i) z ≤ c i}
  | 0, N, c => by
      have he : {z : ℤ × ℤ | ∀ i : Fin 0, dot (N i) z ≤ c i} = Set.univ := by
        ext z; simp
      rw [he]; exact isLatticeConvexRegion_univ
  | (k+1), N, c => by
      have he : {z : ℤ × ℤ | ∀ i : Fin (k+1), dot (N i) z ≤ c i}
          = {z : ℤ × ℤ | ∀ i : Fin k, dot (N i.castSucc) z ≤ c i.castSucc}
              ∩ halfPlaneLE (N (Fin.last k)) (c (Fin.last k)) := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, halfPlaneLE]
        constructor
        · intro h
          exact ⟨fun i => h i.castSucc, h (Fin.last k)⟩
        · rintro ⟨h1, h2⟩ i
          exact Fin.lastCases h2 h1 i
      rw [he]
      exact isLatticeConvexRegion_inter_halfPlaneLE _ _
        (isLatticeConvexRegion_iInter_halfPlaneLE k
          (fun i => N i.castSucc) (fun i => c i.castSucc))

/-- The region a `Fin n`-indexed list of half-plane constraints cuts out. -/
def PolyShapeOf {n : ℕ} (N : Fin n → ℤ × ℤ) (c : Fin n → ℤ) : Set (ℤ × ℤ) :=
  {z | ∀ i, dot (N i) z ≤ c i}

theorem isLatticeConvexRegion_PolyShapeOf {n : ℕ} (N : Fin n → ℤ × ℤ) (c : Fin n → ℤ) :
    IsLatticeConvexRegion (PolyShapeOf N c) :=
  isLatticeConvexRegion_iInter_halfPlaneLE n N c

/-- **The `2m`-gon fan structure, Round 91 shape.** `hccw` is gone; `hadj` is the `E T`-membership
"nothing strictly between consecutive normals" guard already established by
`adjacent_shared_vertex`/`mem_face_of_adjacent_endpoint_ccw`, and `hEeq`/`hlc` carry the real
underlying region's data as fields rather than deriving it from `det`-positivity alone. -/
structure PolyFan (m : ℕ) [NeZero m] where
  N : Fin (2 * m) → ℤ × ℤ
  c : Fin (2 * m) → ℤ
  v : Fin (2 * m) → ℤ × ℤ
  T : Set (ℤ × ℤ)
  hTdef : T = PolyShapeOf N c
  hlc : IsLatticeConvexRegion T
  hEeq : E T = Set.range N
  hprim : ∀ i, Prim (N i)
  hadj : ∀ i : Fin (2 * m), ∀ μ ∈ E T, ¬(0 < det (N i) μ ∧ 0 < det μ (N (i + 1)))
  hanti : ∀ i, N (i + (⟨m, by have := NeZero.pos m; omega⟩ : Fin (2 * m))) = -N i
  htight1 : ∀ i, dot (N i) (v i) = c i
  htight2 : ∀ i, dot (N (i + 1)) (v i) = c (i + 1)
  hv_mem : ∀ i j, dot (N j) (v i) ≤ c j

def PolyShape {m : ℕ} [NeZero m] (F : PolyFan m) : Set (ℤ × ℤ) := PolyShapeOf F.N F.c

/-- **`E (PolyShape F) ⊆ Set.range F.N`**, near-immediate given `hTdef`/`hEeq` as fields: this is
exactly the containment `E_hexShape`'s `⊆` direction needs to generalize past `m = 3`, once `T`
is instantiated with real geometric data. -/
theorem E_PolyShape_subset_range {m : ℕ} [NeZero m] (F : PolyFan m) :
    E (PolyShape F) ⊆ Set.range F.N := by
  have h : PolyShape F = F.T := by rw [F.hTdef]; rfl
  rw [h, F.hEeq]

/-- **`Set.range F.N ⊆ E (PolyShape F)`**, the reverse containment: every fan normal really is an
edge normal, witnessed by its two flanking tight vertices `v i` and `v (i-1)`. This needs `v i ≠
v (i-1)` as an extra hypothesis — bare `htight1/2`/`hv_mem` don't rule out a degenerate fan where
three or more consecutive normals share one vertex, and that degeneracy is exactly the kind of
fact Round 91 deferred to real geometric instantiation rather than trying to derive abstractly. -/
theorem range_subset_E_PolyShape {m : ℕ} [NeZero m] (F : PolyFan m)
    (hvne : ∀ i : Fin (2 * m), F.v i ≠ F.v (i - 1)) :
    Set.range F.N ⊆ E (PolyShape F) := by
  rintro _ ⟨i, rfl⟩
  refine ⟨F.hprim i, F.v i, ?_, F.v (i - 1), ?_, hvne i⟩
  · refine ⟨(fun j => F.hv_mem i j), fun y hy => ?_⟩
    have := hy i
    rw [F.htight1 i]; exact this
  · refine ⟨(fun j => F.hv_mem (i - 1) j), fun y hy => ?_⟩
    have heq : i - 1 + 1 = i := sub_add_cancel i 1
    have hti := F.htight2 (i - 1)
    rw [heq] at hti
    have := hy i
    rw [hti]; exact this

/-! ## `hexFan3`: the `m = 3` sanity instance under the Round 91 struct

`T := PolyShapeOf N c` is literally `Nivat.ShellSweep.hexShape 2 2 1 1 0` after unfolding the six
coordinate inequalities into `dot`-form; `hEeq` and `hlc` then come for free from the already-
landed `E_hexShape`/`isLatticeConvexRegion_hexShape` (`ShellSweep.lean:226,250`) instead of being
proved from scratch — this is the reuse `E_PolyShape_subset_range`'s docstring anticipated. -/

open Nivat.ShellSweep

def hex3N : Fin 6 → ℤ × ℤ := ![(1,0), (0,1), (-1,1), (-1,0), (0,-1), (1,-1)]
def hex3c : Fin 6 → ℤ := ![2, 2, 1, 0, 0, 1]
def hex3v : Fin 6 → ℤ × ℤ := ![(2,2), (1,2), (0,1), (0,0), (1,0), (2,1)]

theorem hex3_T_eq : PolyShapeOf hex3N hex3c = hexShape 2 2 1 1 0 := by
  ext z
  simp only [PolyShapeOf, hex3N, hex3c, mem_hexShape, Set.mem_ofPred_eq]
  constructor
  · intro h
    have h0 := h 0; have h1 := h 1; have h2 := h 2
    have h3 := h 3; have h4 := h 4; have h5 := h 5
    simp [dot] at h0 h1 h2 h3 h4 h5
    omega
  · intro h i
    fin_cases i <;> simp [dot] <;> omega

theorem hex3_nondeg : Nondeg 2 2 1 1 0 := ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem hex3_range_eq : Set.range hex3N = hexE := by
  apply Set.Subset.antisymm
  · rintro _ ⟨i, rfl⟩; fin_cases i <;> simp [hex3N, hexE]
  · intro x hx
    simp only [hexE, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨2, rfl⟩

def hexFan3 : PolyFan 3 where
  N := hex3N
  c := hex3c
  v := hex3v
  T := PolyShapeOf hex3N hex3c
  hTdef := rfl
  hlc := isLatticeConvexRegion_PolyShapeOf hex3N hex3c
  hEeq := by rw [hex3_T_eq, E_hexShape hex3_nondeg, hex3_range_eq]
  hprim := by decide
  hadj := by
    intro i μ hμ hcon
    rw [hex3_T_eq, E_hexShape hex3_nondeg, ← hex3_range_eq] at hμ
    obtain ⟨j, rfl⟩ := hμ
    fin_cases i <;> fin_cases j <;> revert hcon <;> decide
  hanti := by decide
  htight1 := by decide
  htight2 := by decide
  hv_mem := by decide

/-- `hexFan3`'s six vertices are pairwise-consecutive-distinct, closing the last hypothesis
`range_subset_E_PolyShape` needs to give `Set.range hexFan3.N ⊆ E (PolyShape hexFan3)` — combined
with `E_PolyShape_subset_range`, this gives the full equality `E (PolyShape hexFan3) =
Set.range hexFan3.N` end to end on a real, non-vacuous instance. -/
theorem hexFan3_hvne : ∀ i : Fin 6, hexFan3.v i ≠ hexFan3.v (i - 1) := by decide

theorem hexFan3_E_eq_range : E (PolyShape hexFan3) = Set.range hexFan3.N :=
  Set.Subset.antisymm (E_PolyShape_subset_range hexFan3)
    (range_subset_E_PolyShape hexFan3 hexFan3_hvne)

/-! ## Toward the general bracket-existence lemma

The consumer-facing goal is: for **arbitrary** `PolyFan m` data (not just `hexFan3`) and an
arbitrary primitive `n ∉ Set.range F.N`, locate the bracket `i` with `0 < det (F.N i) n` and
`0 < det n (F.N (i+1))`, then collapse `face (PolyShape F) n` to `{F.v i}`. The collapse step,
once `i` is in hand, is already fully general — `face_subset_singleton_of_bracket` below is
exactly `face_subset_singleton_of_between` restated in `PolyFan` vocabulary, using `hv_mem`/
`htight1`/`htight2` to supply the shared-vertex data. It needs no new hypothesis and holds for
every `PolyFan m`.

What is **not** yet general is locating `i` in the first place. That needs a genuine coverage
fact: "the `2m` open cones `{n | 0 < det (N i) n ∧ 0 < det n (N (i+1))}` partition
`(ℤ×ℤ) \ Set.range N`" — equivalently, that `N`, read in index order, winds around the origin
exactly once. `hEeq`/`hadj` pin down *local* adjacency (nothing else in `E T` sits between two
consecutive normals) but say nothing about *global* coverage — the same gap Round 91 flagged for
the old `hccw`-only design, now relocated one level up (`lane-cd-fanscope.lean`'s `badFan` is
exactly a coverage failure: 3 distinct normals visited twice each, never covering the other 3
directions the true hexagon would need). For `hexFan3` this coverage fact comes for free via
`face_subsingleton_hexShape`'s six-way coordinate case split (`ShellSweep.lean:174`), because
that lemma is proved directly against `hexShape`'s explicit box-plus-diagonal description, not
against the fan data abstractly. Genuinely generalizing it — proving coverage for an *arbitrary*
`2m`-gon fan, or extracting it from `DecompData.Sphi`'s real geometry via `Sphi_negSymm`
(`DecompData.lean:412-425`) plus boundedness of `Sphi` — is the one piece of new math this file
does not yet supply, and is the natural next lane task. -/

/-- **Once the bracket index is known, the collapse is fully general** — no per-instance work
needed beyond supplying `i`. This is `face_subset_singleton_of_between` restated against a
`PolyFan`'s own `hv_mem`/`htight1`/`htight2` fields. -/
theorem face_subset_singleton_of_bracket {m : ℕ} [NeZero m] (F : PolyFan m) {n : ℤ × ℤ}
    (i : Fin (2 * m)) (hD : 0 < det (F.N i) (F.N (i + 1)))
    (hα : 0 < det n (F.N (i + 1))) (hβ : 0 < det (F.N i) n) :
    face (PolyShape F) n ⊆ {F.v i} :=
  face_subset_singleton_of_between hD hα hβ (fun z hz => hz i) (fun z hz => hz (i + 1))
    (fun j => F.hv_mem i j) (F.htight1 i) (F.htight2 i)

end Nivat.TwoMGon

#print axioms Nivat.TwoMGon.cramer_dot
#print axioms Nivat.TwoMGon.face_subset_singleton_of_cone'
#print axioms Nivat.TwoMGon.face_subset_singleton_of_between
#print axioms Nivat.TwoMGon.det_pos_cross_of_half0
#print axioms Nivat.TwoMGon.det_pos_cross_of_half1
#print axioms Nivat.TwoMGon.det_neg_neg
#print axioms Nivat.TwoMGon.half_eq_one_iff'
#print axioms Nivat.TwoMGon.det_pos_of_cycBtw_short
#print axioms Nivat.TwoMGon.isLatticeConvexRegion_iInter_halfPlaneLE
#print axioms Nivat.TwoMGon.isLatticeConvexRegion_PolyShapeOf
#print axioms Nivat.TwoMGon.E_PolyShape_subset_range
#print axioms Nivat.TwoMGon.range_subset_E_PolyShape
#print axioms Nivat.TwoMGon.hexFan3
#print axioms Nivat.TwoMGon.hexFan3_hvne
#print axioms Nivat.TwoMGon.hexFan3_E_eq_range
#print axioms Nivat.TwoMGon.face_subset_singleton_of_bracket
