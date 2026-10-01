/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Defs.Config
import Nivat.Defs.Complexity
import Nivat.Defs.Orbit
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Int.LeastGreatest

/-!
# Finiteness of periodic configurations with a bounded period lattice

Formalisation of the counting core of §8.4, Lemma 8.16 of *The Convex Nivat Conjecture*
(Pan).

The key combinatorial fact is: if `α` is finite and `(v, u)` is a unimodular basis of `ℤ²`,
then a configuration `G : ℤ² → α` periodic under `k • v` and `m • u` is completely determined
by its values on the finite fundamental domain `{s • v + t • u | 0 ≤ s < k, 0 ≤ t < m}`. Hence
there are at most `|α| ^ (k * m)` such configurations. This is the "period lattice controlled
by a fixed lower bound gives finitely many bi-periodic configurations" step used to show the
limit set `Ω` in Lemma 8.16 is finite.

Paper §8.4 (`nivat.txt:1713`) also defines the *trace* of a doubly periodic configuration `y`
along a primitive vector `v`: `Tr(y) := min {π(τ) : τ ∈ Per(y), π(τ) > 0}`, where `π := pi v`.
This file sets that up too, as the period bound that controls Lemma 8.16's finiteness argument.

## Main definitions

* `Nivat.modFin` — reduction of an integer modulo `k` into `Fin k`.
* `Nivat.fold` — the fundamental-domain coordinates of `z` with respect to a unimodular basis
  `(v, u)` and moduli `(k, m)`.
* `Nivat.trace` — `Tr(y)`, the least positive value of `pi v` on `Per y`.

## Main results

* `Nivat.G_eq_of_fold_eq` — `G` is determined by `fold`, given the two periods.
* `Nivat.exists_eq_comp_fold` — `G = g ∘ fold` for some `g : Fin k × Fin m → α`.
* `Nivat.finite_setOf_mem_Per` — the set of configurations periodic under `k • v` and `m • u`
  is finite, when `α` is finite.
* `Nivat.exists_pos_smul_mem_Per` — a doubly periodic configuration periodic under `k • v` has
  some positive multiple of `u` as a period too.
* `Nivat.Set.Finite.of_common_periods` — a family of configurations sharing a coarse period
  `k • v` and a common bound `m • u` on the second period is finite.
* `Nivat.finite_of_doublyPeriodic_of_mem_Per` — downstream-friendly finiteness statement for a
  set of doubly periodic configurations with shared/bounded periods.
* `Nivat.trace_pos` — `Tr(y) > 0` when `v` is primitive and `y` is doubly periodic.
* `Nivat.exists_mem_Per_pi_eq_trace` — `Tr(y)` is attained: some `τ ∈ Per y` has `pi v τ = Tr(y)`.
* `Nivat.finite_of_trace_le` — trace-bounded doubly periodic configurations sharing a coarse
  period `k • v` are finite, over a finite alphabet (paper `nivat.txt:1716`–`1721`).
* `Nivat.exists_mem_subseqLimits_agree` — compactness extraction: a sequence of elements of
  `subseqLimits G d` has a further limit point also in `subseqLimits G d`, agreeing with terms
  of arbitrarily large index on any finite window.
* `Nivat.eq_on_row_of_eq_on_range`, `Nivat.eq_on_row_of_eq_on_BWin` — two `k • v`-periodic
  configurations agreeing at `k` consecutive points of a row (resp. on the window `BWin v u W`
  with `W ≥ k`) agree on the whole row.
* `Nivat.T_zsmul_mem_subseqLimits` — `subseqLimits G d` is invariant under `T (q • d)` for every
  integer `q` (not just `q = ±1`).
* `Nivat.Per_T` — translating a configuration by any `c` does not change its period group.
* `Nivat.exists_infinite_fiber` — pigeonhole: `ℕ → β` with `β` finite has an infinite fiber.
* `Nivat.enumInfinite`/`Nivat.enumInfinite_mem`/`Nivat.le_enumInfinite` — a strictly increasing
  enumeration of an infinite set of naturals, landing in the set and eventually exceeding any
  bound; used to pick "arbitrarily late" indices out of an infinite index set.
* `Nivat.exists_bad_row_or_good` — the bilateral bad-row dichotomy: either `ϖ ∈ Per y` outright,
  or there is an extremal bad row strictly left of `-n` or strictly right of `n - P₀`.
* `Nivat.shift_bad_and_good` — translating by `q := ⌈-x/δ⌉` moves a bad row at `x` to a fixed
  row `r ∈ [0, δ)`, transporting both the badness witness and the good-interval fact.
* `Nivat.Per.apply_of_sub`, `Nivat.reduce_bad_to_window` — if `a - b` is a period of `y`, `y`
  agrees at `a + c`/`b + c` for any `c`; used to reduce the "s-coordinate" of a bad point modulo
  `k` (via the known period `k • v`) without disturbing the badness witness.

<!-- TODO(lineV): the remaining Step 1b content — boundedness of `trace v` on `subseqLimits G d`
(paper §8.4, Lemma 8.16, "Step 1: Ω is finite"). The lemmas above are all the reusable
infrastructure for it (row agreement, arbitrary-shift invariance, pigeonhole, enumeration, the
bad-row dichotomy); the top-level argument is still to be assembled:
* by_contra a bound on `trace v` on `Ω`, giving `y : ℕ → Ω` with `trace v (y n) ≥ n`;
* `exists_mem_subseqLimits_agree` on `y` gives `θ ∈ Ω`, doubly periodic, with
  `ϖ ∈ Per θ`, `pi v ϖ = trace v θ =: P₀`;
* for each `n`, `eq_on_row_of_eq_on_BWin`-style agreement between `θ` and `y (m n)` on rows
  `[-n, n - P₀]` feeds `exists_bad_row_or_good`: either every such row is `ϖ`-good for
  `y (m n)` (which forces `ϖ ∈ Per (y (m n))`, hence `trace v (y (m n)) ≤ P₀` — a direct
  contradiction for `n > P₀`), or there is an extremal bad row `x n` strictly left of `-n` or
  strictly right of `n - P₀` (already proved bilaterally by `exists_bad_row_or_good`);
* shifting by `q n := ⌈-(x n)/δ⌉` (where `δ := -(pi v d) > 0`) via `T_zsmul_mem_subseqLimits`
  moves the bad row to a fixed `r n ∈ [0, δ)`, transporting the good-interval and badness facts
  too (`shift_bad_and_good`); reducing its "s-coordinate" mod `k` (via `Per_T`
  and the period `k • v`, preserved by the shift) lands a witness of the (still transferred) bad
  inequality inside the *finite* window `F := {s • v + t • u : 0 ≤ s < k, 0 ≤ t < δ}`
  (`reduce_bad_to_window`); `exists_infinite_fiber` then gives a single `z_* ∈ F` that is the
  reduced bad point for infinitely many `n`;
* a second application of `exists_mem_subseqLimits_agree` (via `enumInfinite` to turn that
  infinite index set into a sequence) extracts `y ∈ Ω`, doubly periodic, agreeing with some
  shifted `y (m n)` on any finite window including `{z_*, z_* + ϖ}` — transferring both the bad
  inequality `y (z_* + ϖ) ≠ y z_*` and (in the limit) `ϖ`-goodness on every row `> pi v z_*`;
  taking any `λ ∈ Per y` with `pi v λ = trace v y > 0` (via `exists_mem_Per_pi_eq_trace`), the row
  of `z_* + λ` already exceeds `pi v z_*` (no need to search for a large multiple `M`, unlike the
  paper's version — one step suffices here), so `Per.apply` on `λ` plus that goodness fact forces
  `y (z_* + ϖ) = y z_*`, contradiction.
This is a genuine bilateral case split (left bad row vs. right bad row) that resists merging into
a single code path — confirmed by direct attempts to eliminate it via `ϖ ↦ -ϖ` / `v ↦ -v`
relabelling, which change which side is symmetric to which but not the two-sidedness itself. -->

## Status

No `sorry`. `Nivat.finite_of_trace_le` and everything above it is complete and used by the rest
of the team. The Step 1b lemmas immediately above it (`exists_mem_subseqLimits_agree` through
`reduce_bad_to_window`) are complete, reusable infrastructure. The top-level boundedness-of-`trace v`
result itself (towards `finite_subseqLimits`) is still in progress — see the `TODO(lineV)` note
above for the full argument and exactly what remains; nothing claiming that result has been
added to this file yet.
-/

namespace Nivat

variable {α : Type*}

/-- The set of positive values `pi v` takes on `Per y`; nonempty exactly when some period of
`y` is not parallel to `v`, which `trace_nonempty` shows holds whenever `y` is doubly periodic
and `v` is primitive. -/
def traceSet (v : ℤ × ℤ) (y : Config α) : Set ℕ := {n : ℕ | 0 < n ∧ ∃ τ ∈ Per y, pi v τ = (n : ℤ)}

/-- If `v` is primitive and `y` is doubly periodic, some period of `y` is not parallel to `v`,
i.e. `pi v` does not vanish on both of the two linearly independent periods witnessing
`DoublyPeriodic y`. -/
theorem traceSet_nonempty {v : ℤ × ℤ} (hv : Primitive v) {y : Config α}
    (hy : DoublyPeriodic y) : (traceSet v y).Nonempty := by
  classical
  obtain ⟨a, ha, b, hb, hdet⟩ := hy
  obtain ⟨u, hvu⟩ := hv.exists_dual
  have hor : pi v a ≠ 0 ∨ pi v b ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨hpa, hpb⟩ := h
    have hea : a = (det a u) • v := by
      have h := eq_smul_add_smul hvu a
      rwa [show det v a = pi v a from rfl, hpa, zero_smul, add_zero] at h
    have heb : b = (det b u) • v := by
      have h := eq_smul_add_smul hvu b
      rwa [show det v b = pi v b from rfl, hpb, zero_smul, add_zero] at h
    apply hdet
    rw [hea, heb]
    simp only [det, Prod.smul_def, smul_eq_mul]
    ring
  -- From a period `τ` with `pi v τ ≠ 0`, get a period with `pi v` a *positive* value: `τ` itself
  -- if `pi v τ > 0`, else `-τ` (also a period, since `Per y` is a subgroup).
  have hmem : ∀ τ ∈ Per y, pi v τ ≠ 0 → (traceSet v y).Nonempty := by
    intro τ hτ hτne
    rcases lt_or_gt_of_ne hτne with hlt | hgt
    · have hcast : ((-(pi v τ)).toNat : ℤ) = -(pi v τ) := Int.toNat_of_nonneg (by omega)
      refine ⟨(-(pi v τ)).toNat, by exact_mod_cast (by omega : (0:ℤ) < ((-(pi v τ)).toNat : ℤ)),
        -τ, AddSubgroup.neg_mem _ hτ, ?_⟩
      have hneg : pi v (-τ) = -(pi v τ) := by
        rw [show (-τ : ℤ × ℤ) = (-1 : ℤ) • τ from (neg_one_smul ℤ τ).symm, pi_smul]; ring
      rw [hneg, hcast]
    · have hcast : ((pi v τ).toNat : ℤ) = pi v τ := Int.toNat_of_nonneg (by omega)
      exact ⟨(pi v τ).toNat, by exact_mod_cast (by omega : (0:ℤ) < ((pi v τ).toNat : ℤ)),
        τ, hτ, hcast.symm⟩
  rcases hor with h | h
  · exact hmem a ha h
  · exact hmem b hb h

/-- **Trace** of a doubly periodic configuration `y` along the primitive vector `v`: the least
positive value taken by `pi v` on `Per y`. Paper §8.4, `nivat.txt:1713`:
`Tr(y) := min {π(τ) : τ ∈ Per(y), π(τ) > 0}`. -/
noncomputable def trace (v : ℤ × ℤ) (y : Config α) : ℕ := sInf (traceSet v y)

/-- The trace is attained: there is a period `τ` of `y` with `pi v τ = Tr(y)`. -/
theorem exists_mem_Per_pi_eq_trace {v : ℤ × ℤ} (hv : Primitive v) {y : Config α}
    (hy : DoublyPeriodic y) : ∃ τ ∈ Per y, pi v τ = (trace v y : ℤ) := by
  obtain ⟨-, τ, hτ, heq⟩ := Nat.sInf_mem (traceSet_nonempty hv hy)
  exact ⟨τ, hτ, heq⟩

/-- `Tr(y) > 0` whenever `v` is primitive and `y` is doubly periodic. -/
theorem trace_pos {v : ℤ × ℤ} (hv : Primitive v) {y : Config α} (hy : DoublyPeriodic y) :
    0 < trace v y := (Nat.sInf_mem (traceSet_nonempty hv hy)).1

/-- Reduction of an integer `s` modulo `k` into `Fin k`, for `0 < k`. -/
def modFin (k : ℕ) (hk : 0 < k) (s : ℤ) : Fin k :=
  ⟨(s % (k : ℤ)).toNat, by
    have hkZ : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
    have h1 : 0 ≤ s % (k : ℤ) := Int.emod_nonneg s hkZ
    have h2 : s % (k : ℤ) < (k : ℤ) := Int.emod_lt_of_pos s (by exact_mod_cast hk)
    omega⟩

/-- The value of `modFin k hk s` as an integer is `s % k`. -/
theorem modFin_val (k : ℕ) (hk : 0 < k) (s : ℤ) :
    ((modFin k hk s).val : ℤ) = s % (k : ℤ) := by
  have hkZ : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  exact Int.toNat_of_nonneg (Int.emod_nonneg s hkZ)

/-- `modFin` applied to a value already in `Fin k` (viewed in `ℤ`) returns it unchanged. -/
theorem modFin_natCast (k : ℕ) (hk : 0 < k) (n : Fin k) :
    modFin k hk (n.val : ℤ) = n := by
  have h1 : (0 : ℤ) ≤ (n.val : ℤ) := Int.natCast_nonneg _
  have h2 : (n.val : ℤ) < (k : ℤ) := by exact_mod_cast n.isLt
  apply Fin.ext
  show ((n.val : ℤ) % (k : ℤ)).toNat = n.val
  rw [Int.emod_eq_of_lt h1 h2, Int.toNat_natCast]

/-- If `k • v` is a period of `G`, then `G` at `s • v + t • u` only depends on `s` modulo `k`. -/
theorem G_reduce_fst {G : Config α} {v u : ℤ × ℤ} {k : ℕ} (hk : 0 < k)
    (hper : ((k : ℤ) • v) ∈ Per G) (s t : ℤ) :
    G (s • v + t • u) = G (((modFin k hk s).val : ℤ) • v + t • u) := by
  have hkZ : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  have hval : ((modFin k hk s).val : ℤ) = s % (k : ℤ) := modFin_val k hk s
  have heuc : (k : ℤ) * (s / (k : ℤ)) + s % (k : ℤ) = s := Int.mul_ediv_add_emod s (k : ℤ)
  have hsplit : (s % (k : ℤ)) • v + (s / (k : ℤ)) • ((k : ℤ) • v) = s • v := by
    rw [show (s / (k : ℤ)) • ((k : ℤ) • v) = ((s / (k : ℤ)) * (k : ℤ)) • v from
      (mul_smul _ _ _).symm, ← add_smul]
    congr 1
    linear_combination heuc
  have heq : s • v + t • u
      = (((modFin k hk s).val : ℤ) • v + t • u) + (s / (k : ℤ)) • ((k : ℤ) • v) := by
    rw [hval, ← hsplit]; abel
  have hmem : (s / (k : ℤ)) • ((k : ℤ) • v) ∈ Per G := AddSubgroup.zsmul_mem _ hper _
  rw [heq, Per.apply hmem]

/-- If `m • u` is a period of `G`, then `G` at `s • v + t • u` only depends on `t` modulo `m`. -/
theorem G_reduce_snd {G : Config α} {v u : ℤ × ℤ} {m : ℕ} (hm : 0 < m)
    (hper : ((m : ℤ) • u) ∈ Per G) (s t : ℤ) :
    G (s • v + t • u) = G (s • v + ((modFin m hm t).val : ℤ) • u) := by
  have hmZ : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hval : ((modFin m hm t).val : ℤ) = t % (m : ℤ) := modFin_val m hm t
  have heuc : (m : ℤ) * (t / (m : ℤ)) + t % (m : ℤ) = t := Int.mul_ediv_add_emod t (m : ℤ)
  have hsplit : (t % (m : ℤ)) • u + (t / (m : ℤ)) • ((m : ℤ) • u) = t • u := by
    rw [show (t / (m : ℤ)) • ((m : ℤ) • u) = ((t / (m : ℤ)) * (m : ℤ)) • u from
      (mul_smul _ _ _).symm, ← add_smul]
    congr 1
    linear_combination heuc
  have heq : s • v + t • u
      = (s • v + ((modFin m hm t).val : ℤ) • u) + (t / (m : ℤ)) • ((m : ℤ) • u) := by
    rw [hval, ← hsplit]; abel
  have hmem : (t / (m : ℤ)) • ((m : ℤ) • u) ∈ Per G := AddSubgroup.zsmul_mem _ hper _
  rw [heq, Per.apply hmem]

/-- The fundamental-domain coordinates of `z` with respect to the unimodular basis `(v, u)`,
i.e. its `(v, u)`-coordinates reduced modulo `(k, m)`. -/
def fold (v u : ℤ × ℤ) (k m : ℕ) (hk : 0 < k) (hm : 0 < m) (z : ℤ × ℤ) : Fin k × Fin m :=
  (modFin k hk (det z u), modFin m hm (det v z))

/-- **Key lemma.** If `k • v` and `m • u` are both periods of `G`, then `G` is determined by
`fold v u k m z`: its value at `z` equals its value at the representative point of `z`'s
fundamental-domain cell. -/
theorem G_eq_of_fold {α : Type*} {G : Config α} {v u : ℤ × ℤ} (hvu : det v u = 1)
    {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (hperv : ((k : ℤ) • v) ∈ Per G)
    (hperu : ((m : ℤ) • u) ∈ Per G) (z : ℤ × ℤ) :
    G z = G (((fold v u k m hk hm z).1.val : ℤ) • v + ((fold v u k m hk hm z).2.val : ℤ) • u) := by
  have hz : z = (det z u) • v + (det v z) • u := eq_smul_add_smul hvu z
  calc
    G z = G ((det z u) • v + (det v z) • u) := congrArg G hz
    _ = G (((modFin k hk (det z u)).val : ℤ) • v + (det v z) • u) :=
      G_reduce_fst hk hperv (det z u) (det v z)
    _ = G (((modFin k hk (det z u)).val : ℤ) • v
          + ((modFin m hm (det v z)).val : ℤ) • u) :=
      G_reduce_snd hm hperu (((modFin k hk (det z u)).val : ℤ)) (det v z)

/-- If `G₁` and `G₂` are both periodic under `k • v` and `m • u` and agree on `fold`, i.e. on
every fundamental-domain representative point, then `G₁ = G₂`. -/
theorem G_eq_of_fold_eq {α : Type*} {G₁ G₂ : Config α} {v u : ℤ × ℤ} (hvu : det v u = 1)
    {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (hperv₁ : ((k : ℤ) • v) ∈ Per G₁)
    (hperu₁ : ((m : ℤ) • u) ∈ Per G₁) (hperv₂ : ((k : ℤ) • v) ∈ Per G₂)
    (hperu₂ : ((m : ℤ) • u) ∈ Per G₂)
    (hrep : ∀ p : Fin k × Fin m,
      G₁ ((p.1.val : ℤ) • v + (p.2.val : ℤ) • u) = G₂ ((p.1.val : ℤ) • v + (p.2.val : ℤ) • u)) :
    G₁ = G₂ := by
  funext z
  rw [G_eq_of_fold hvu hk hm hperv₁ hperu₁ z, G_eq_of_fold hvu hk hm hperv₂ hperu₂ z, hrep]

/-- Any `G` periodic under `k • v` and `m • u` is `g ∘ fold` for some `g : Fin k × Fin m → α`. -/
theorem exists_eq_comp_fold {α : Type*} {G : Config α} {v u : ℤ × ℤ} (hvu : det v u = 1)
    {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (hperv : ((k : ℤ) • v) ∈ Per G)
    (hperu : ((m : ℤ) • u) ∈ Per G) :
    ∃ g : Fin k × Fin m → α, ∀ z, G z = g (fold v u k m hk hm z) :=
  ⟨fun p => G ((p.1.val : ℤ) • v + (p.2.val : ℤ) • u),
    fun z => G_eq_of_fold hvu hk hm hperv hperu z⟩

/-- **Main finiteness result.** With a fixed unimodular basis `(v, u)` and fixed positive moduli
`(k, m)`, over a finite alphabet `α` there are only finitely many configurations periodic under
both `k • v` and `m • u`. -/
theorem finite_setOf_mem_Per {α : Type*} [Finite α] {v u : ℤ × ℤ} (hvu : det v u = 1)
    {k m : ℕ} (hk : 0 < k) (hm : 0 < m) :
    {G : Config α | ((k : ℤ) • v) ∈ Per G ∧ ((m : ℤ) • u) ∈ Per G}.Finite := by
  classical
  set S := {G : Config α | ((k : ℤ) • v) ∈ Per G ∧ ((m : ℤ) • u) ∈ Per G} with hS
  let Φ : Config α → (Fin k × Fin m → α) := fun G p => G ((p.1.val : ℤ) • v + (p.2.val : ℤ) • u)
  have hinj : Set.InjOn Φ S := by
    rintro G₁ hG₁ G₂ hG₂ hΦ
    obtain ⟨hperv₁, hperu₁⟩ := hG₁
    obtain ⟨hperv₂, hperu₂⟩ := hG₂
    exact G_eq_of_fold_eq hvu hk hm hperv₁ hperu₁ hperv₂ hperu₂ (fun p => congrFun hΦ p)
  have himg : (Φ '' S).Finite := Set.toFinite _
  exact Set.Finite.of_finite_image himg hinj

/-- If `G` is doubly periodic and `k • v` is one of its periods, then some positive multiple of
`u` is also a period of `G`. -/
theorem exists_pos_smul_mem_Per {α : Type*} {G : Config α} {v u : ℤ × ℤ} (_hvu : det v u = 1)
    (hdp : DoublyPeriodic G) : ∃ m : ℕ, 0 < m ∧ ((m : ℤ) • u) ∈ Per G := by
  obtain ⟨a, ha, b, hb, hdet⟩ := hdp
  -- Cramer's rule in the basis `(a, b)`: `det a b • u = (det u b) • a + (det a u) • b`.
  have hcramer : (det a b) • u = (det u b) • a + (det a u) • b := by
    have h1 : (det a b • u).1 = ((det u b) • a + (det a u) • b).1 := by
      show (det a b) * u.1 = (det u b) * a.1 + (det a u) * b.1
      simp only [det]; ring
    have h2 : (det a b • u).2 = ((det u b) • a + (det a u) • b).2 := by
      show (det a b) * u.2 = (det u b) * a.2 + (det a u) * b.2
      simp only [det]; ring
    exact Prod.ext h1 h2
  have hmem : (det a b) • u ∈ Per G := by
    rw [hcramer]
    exact AddSubgroup.add_mem _ (AddSubgroup.zsmul_mem _ ha _) (AddSubgroup.zsmul_mem _ hb _)
  refine ⟨(det a b).natAbs, Int.natAbs_pos.mpr hdet, ?_⟩
  rcases (det a b).natAbs_eq with heq | heq
  · rwa [← heq]
  · have hmem' : (-(((det a b).natAbs : ℤ) • u)) ∈ Per G := by
      rw [← neg_smul, ← heq]; exact hmem
    exact (AddSubgroup.neg_mem_iff _).mp hmem'

/-- A family of configurations sharing a coarse period `k • v`, whose second-direction periods
are all controlled by the same bound `m • u`, is finite. -/
theorem Set.Finite.of_common_periods {α : Type*} [Finite α] {v u : ℤ × ℤ} (hvu : det v u = 1)
    {k m : ℕ} (hk : 0 < k) (hm : 0 < m) {Ω : Set (Config α)}
    (hkv : ∀ G ∈ Ω, ((k : ℤ) • v) ∈ Per G) (hmu : ∀ G ∈ Ω, ((m : ℤ) • u) ∈ Per G) :
    Ω.Finite :=
  (finite_setOf_mem_Per hvu hk hm).subset (fun G hG => ⟨hkv G hG, hmu G hG⟩)

/-- **Downstream-friendly finiteness.** A set of doubly periodic configurations that all share
a coarse period `k • v` and whose second-direction periods are uniformly bounded by `M • u` is
finite. -/
theorem finite_of_doublyPeriodic_of_mem_Per {α : Type*} [Finite α] {v u : ℤ × ℤ}
    (hvu : det v u = 1) {k : ℕ} (hk : 0 < k) {M : ℕ} (hM : 0 < M)
    {Ω : Set (Config α)} (_hdp : ∀ G ∈ Ω, DoublyPeriodic G)
    (hkv : ∀ G ∈ Ω, ((k : ℤ) • v) ∈ Per G)
    (hbd : ∀ G ∈ Ω, ((M : ℤ) • u) ∈ Per G) : Ω.Finite :=
  Set.Finite.of_common_periods hvu hk hM hkv hbd

/-- A unimodular basis vector is primitive: `det v u = 1` gives `u.2, -u.1` as Bézout
coefficients for `v.1, v.2`. -/
theorem Primitive_of_det_eq_one {v u : ℤ × ℤ} (h : det v u = 1) : Primitive v := by
  show IsCoprime v.1 v.2
  refine ⟨u.2, -u.1, ?_⟩
  simp only [det] at h
  linear_combination h

/-- If `s' • v + T • u` is a period of `G`, then `G` at `a • v + b • u` only depends on `b`
modulo `T`, at the cost of shearing the `v`-coefficient by a multiple of `s'`. This is the
one-period analogue of `G_reduce_snd`, used when the second period is not a pure multiple of
`u` but a general shear `s' • v + T • u`. -/
theorem G_reduce_shear {G : Config α} {v u : ℤ × ℤ} {T : ℕ} (hT : 0 < T) {s' : ℤ}
    (hper : (s' • v + (T : ℤ) • u) ∈ Per G) (a b : ℤ) :
    G (a • v + b • u) =
      G ((a - (b / (T : ℤ)) * s') • v + ((modFin T hT b).val : ℤ) • u) := by
  have hval : ((modFin T hT b).val : ℤ) = b % (T : ℤ) := modFin_val T hT b
  have heuc : (T : ℤ) * (b / (T : ℤ)) + b % (T : ℤ) = b := Int.mul_ediv_add_emod b (T : ℤ)
  have heq : a • v + b • u
      = ((a - (b / (T : ℤ)) * s') • v + ((modFin T hT b).val : ℤ) • u)
        + (b / (T : ℤ)) • (s' • v + (T : ℤ) • u) := by
    rw [hval]
    apply Prod.ext
    · show a * v.1 + b * u.1 =
        (a - (b / (T : ℤ)) * s') * v.1 + (b % (T : ℤ)) * u.1
          + (b / (T : ℤ)) * (s' * v.1 + (T : ℤ) * u.1)
      linear_combination (-u.1) * heuc
    · show a * v.2 + b * u.2 =
        (a - (b / (T : ℤ)) * s') * v.2 + (b % (T : ℤ)) * u.2
          + (b / (T : ℤ)) * (s' * v.2 + (T : ℤ) * u.2)
      linear_combination (-u.2) * heuc
  have hmem : (b / (T : ℤ)) • (s' • v + (T : ℤ) • u) ∈ Per G := AddSubgroup.zsmul_mem _ hper _
  rw [heq, Per.apply hmem]

/-- The fundamental-domain coordinates of `z` with respect to the shear lattice generated by
`k • v` and `s' • v + T • u`: the `u`-coefficient of `z` reduced mod `T`, and its `v`-coefficient
(after shearing away the multiple of `s'` induced by that reduction) reduced mod `k`. -/
def foldShear (v u : ℤ × ℤ) (k : ℕ) (hk : 0 < k) (T : ℕ) (hT : 0 < T) (s' : ℤ)
    (z : ℤ × ℤ) : Fin k × Fin T :=
  (modFin k hk (det z u - (det v z / (T : ℤ)) * s'), modFin T hT (det v z))

/-- **Two-step shear reduction.** If `k • v` and `s' • v + T • u` are both periods of `y`, then
`y` is determined by `z`'s `(v, u)`-coordinates reduced to `(Fin k, Fin T)` via the shear. This
is the shear analogue of `G_eq_of_fold`. -/
theorem G_eq_of_shear {y : Config α} {v u : ℤ × ℤ} (hvu : det v u = 1) {k : ℕ} (hk : 0 < k)
    {T : ℕ} (hT : 0 < T) {s' : ℤ} (hperK : ((k : ℤ) • v) ∈ Per y)
    (hperS : (s' • v + (T : ℤ) • u) ∈ Per y) (z : ℤ × ℤ) :
    y z = y (((foldShear v u k hk T hT s' z).1.val : ℤ) • v
           + ((foldShear v u k hk T hT s' z).2.val : ℤ) • u) := by
  have hz : z = (det z u) • v + (det v z) • u := eq_smul_add_smul hvu z
  calc
    y z = y ((det z u) • v + (det v z) • u) := congrArg y hz
    _ = y ((det z u - (det v z / (T : ℤ)) * s') • v + ((modFin T hT (det v z)).val : ℤ) • u) :=
      G_reduce_shear hT hperS (det z u) (det v z)
    _ = y (((modFin k hk (det z u - (det v z / (T : ℤ)) * s')).val : ℤ) • v
          + ((modFin T hT (det v z)).val : ℤ) • u) :=
      G_reduce_fst hk hperK _ _
    _ = y (((foldShear v u k hk T hT s' z).1.val : ℤ) • v
          + ((foldShear v u k hk T hT s' z).2.val : ℤ) • u) := rfl

/-- Two configurations sharing both a coarse period `k • v` and a shear period `s' • v + T • u`,
and agreeing on every fundamental-domain representative of the resulting shear lattice, are
equal. -/
theorem G_eq_of_shear_eq {y₁ y₂ : Config α} {v u : ℤ × ℤ} (hvu : det v u = 1) {k : ℕ}
    (hk : 0 < k) {T : ℕ} (hT : 0 < T) {s' : ℤ} (hperK₁ : ((k : ℤ) • v) ∈ Per y₁)
    (hperS₁ : (s' • v + (T : ℤ) • u) ∈ Per y₁) (hperK₂ : ((k : ℤ) • v) ∈ Per y₂)
    (hperS₂ : (s' • v + (T : ℤ) • u) ∈ Per y₂)
    (hrep : ∀ p : Fin k × Fin T,
      y₁ ((p.1.val : ℤ) • v + (p.2.val : ℤ) • u) = y₂ ((p.1.val : ℤ) • v + (p.2.val : ℤ) • u)) :
    y₁ = y₂ := by
  funext z
  rw [G_eq_of_shear hvu hk hT hperK₁ hperS₁ z, G_eq_of_shear hvu hk hT hperK₂ hperS₂ z, hrep]

/-- Configurations sharing a coarse period `k • v` and a fixed shear period `s' • v + T • u`
(with `T > 0`) are finite in number, over a finite alphabet. -/
theorem finite_setOf_mem_Per_shear {α : Type*} [Finite α] {v u : ℤ × ℤ} (hvu : det v u = 1)
    {k : ℕ} (hk : 0 < k) (s' : ℤ) {T : ℕ} (hT : 0 < T) :
    {y : Config α | ((k : ℤ) • v) ∈ Per y ∧ (s' • v + (T : ℤ) • u) ∈ Per y}.Finite := by
  classical
  set S := {y : Config α | ((k : ℤ) • v) ∈ Per y ∧ (s' • v + (T : ℤ) • u) ∈ Per y} with hS
  let Φ : Config α → (Fin k × Fin T → α) := fun y p => y ((p.1.val : ℤ) • v + (p.2.val : ℤ) • u)
  have hinj : Set.InjOn Φ S := by
    rintro y₁ hy₁ y₂ hy₂ hΦ
    obtain ⟨hperK₁, hperS₁⟩ := hy₁
    obtain ⟨hperK₂, hperS₂⟩ := hy₂
    exact G_eq_of_shear_eq hvu hk hT hperK₁ hperS₁ hperK₂ hperS₂ (fun p => congrFun hΦ p)
  have himg : (Φ '' S).Finite := Set.toFinite _
  exact Set.Finite.of_finite_image himg hinj

/-- **Trace-bounded finiteness** (paper §8.4, `nivat.txt:1716`–`1721`). With a fixed unimodular
basis `(v, u)` and fixed positive `k`, over a finite alphabet there are only finitely many
doubly periodic configurations `y` that are periodic under `k • v` and whose trace `Tr(y)` (the
least positive value `pi v` takes on `Per y`) is at most `P`. -/
theorem finite_of_trace_le {α : Type*} [Finite α] {v u : ℤ × ℤ} (hvu : det v u = 1) {k : ℕ}
    (hk : 0 < k) (P : ℕ) :
    {y : Config α | ((k : ℤ) • v) ∈ Per y ∧ DoublyPeriodic y ∧ trace v y ≤ P}.Finite := by
  classical
  have hv : Primitive v := Primitive_of_det_eq_one hvu
  have hsub : {y : Config α | ((k : ℤ) • v) ∈ Per y ∧ DoublyPeriodic y ∧ trace v y ≤ P} ⊆
      ⋃ s' ∈ (Finset.range k : Finset ℕ), ⋃ T ∈ Finset.Icc 1 P,
        {y : Config α | ((k : ℤ) • v) ∈ Per y ∧ ((s' : ℤ) • v + (T : ℤ) • u) ∈ Per y} := by
    intro y hy
    obtain ⟨hperK, hdp, hle⟩ := hy
    obtain ⟨τ, hτ, hτeq⟩ := exists_mem_Per_pi_eq_trace hv hdp
    have hTpos : 0 < trace v y := trace_pos hv hdp
    set T := trace v y with hTdef
    set s0 := det τ u with hs0def
    have hτdecomp : τ = s0 • v + (T : ℤ) • u := by
      have h := eq_smul_add_smul hvu τ
      rwa [show det v τ = pi v τ from rfl, hτeq] at h
    have hval : ((modFin k hk s0).val : ℤ) = s0 % (k : ℤ) := modFin_val k hk s0
    have heuc : (k : ℤ) * (s0 / (k : ℤ)) + s0 % (k : ℤ) = s0 := Int.mul_ediv_add_emod s0 (k : ℤ)
    have hsplit : (s0 % (k : ℤ)) • v + (s0 / (k : ℤ)) • ((k : ℤ) • v) = s0 • v := by
      rw [show (s0 / (k : ℤ)) • ((k : ℤ) • v) = ((s0 / (k : ℤ)) * (k : ℤ)) • v from
        (mul_smul _ _ _).symm, ← add_smul]
      congr 1
      linear_combination heuc
    have heqmod : τ = ((modFin k hk s0).val : ℤ) • v + (T : ℤ) • u
        + (s0 / (k : ℤ)) • ((k : ℤ) • v) := by
      rw [hτdecomp, hval, ← hsplit]; abel
    have hkey : ((modFin k hk s0).val : ℤ) • v + (T : ℤ) • u
        = τ - (s0 / (k : ℤ)) • ((k : ℤ) • v) := by
      rw [heqmod]; abel
    have hτ' : ((modFin k hk s0).val : ℤ) • v + (T : ℤ) • u ∈ Per y := by
      rw [hkey]
      exact AddSubgroup.sub_mem _ hτ (AddSubgroup.zsmul_mem _ hperK _)
    refine Set.mem_biUnion (Finset.mem_range.mpr (modFin k hk s0).isLt) ?_
    exact Set.mem_biUnion (Finset.mem_Icc.mpr ⟨hTpos, hle⟩) ⟨hperK, hτ'⟩
  have hfin : (⋃ s' ∈ (Finset.range k : Finset ℕ), ⋃ T ∈ Finset.Icc 1 P,
      {y : Config α | ((k : ℤ) • v) ∈ Per y ∧ ((s' : ℤ) • v + (T : ℤ) • u) ∈ Per y}).Finite := by
    apply Set.Finite.biUnion (Finset.range k).finite_toSet
    intro s' _
    apply Set.Finite.biUnion (Finset.Icc 1 P).finite_toSet
    intro T hT
    exact finite_setOf_mem_Per_shear hvu hk (s' : ℤ) (Finset.mem_Icc.mp hT).1
  exact hfin.subset hsub

/-! ## Step 1b infrastructure: boundedness of the trace on `subseqLimits`

The remaining lemmas build towards `nivat.txt`/paper §8.4 Lemma 8.16, "Step 1: `Ω` is
finite", where `Ω := subseqLimits G d`.  `finite_of_trace_le` above handles the easy half
("`{y ∈ Ω : Tr(y) ≤ P}` is finite for every `P`"); what remains is the pigeonhole argument
showing `Tr` is *bounded* on all of `Ω`, not just on some given sublevel set. -/

/-- **Diagonal compactness extraction.** If every term of a sequence `y : ℕ → Config α` lies in
`subseqLimits G d`, some further pointwise-limit point `θ` also lies in `subseqLimits G d`, and
moreover `θ` agrees with `y m` on any finite window, for arbitrarily large `m`.

This upgrades `subseqLimits_nonempty`'s ultrafilter argument by one layer: an ultrafilter on the
sequence index picks out `θ` as a pointwise limit of the `y m`, and then, since each `y m` is
itself already a limit point of `G`'s orbit, `θ` inherits membership in `subseqLimits G d`. -/
theorem exists_mem_subseqLimits_agree {α : Type*} [Finite α] {G : Config α} {d : ℤ × ℤ}
    (y : ℕ → Config α) (hy : ∀ n, y n ∈ subseqLimits G d) :
    ∃ θ : Config α, θ ∈ subseqLimits G d ∧
      ∀ (W : Finset (ℤ × ℤ)) (M : ℕ), ∃ m, M ≤ m ∧ ∀ w ∈ W, θ w = y m w := by
  classical
  set 𝔲 : Ultrafilter ℕ := Ultrafilter.of Filter.atTop with h𝔲
  have key : ∀ w : ℤ × ℤ, ∃ a : α, {m : ℕ | y m w = a} ∈ 𝔲 := by
    intro w
    obtain ⟨a, ha⟩ := Ultrafilter.eq_pure_of_finite (Ultrafilter.map (fun m => y m w) 𝔲)
    refine ⟨a, ?_⟩
    have hmem : ({a} : Set α) ∈ Ultrafilter.map (fun m => y m w) 𝔲 := by
      rw [ha]; exact Ultrafilter.mem_pure.mpr rfl
    rwa [Ultrafilter.mem_map] at hmem
  choose θ hθ using key
  have hagree : ∀ (W : Finset (ℤ × ℤ)) (M : ℕ), ∃ m, M ≤ m ∧ ∀ w ∈ W, θ w = y m w := by
    intro W M
    have h1 : {m : ℕ | M ≤ m} ∈ 𝔲 := Ultrafilter.of_le Filter.atTop (Filter.mem_atTop M)
    have h2 : (⋂ w ∈ W, {m : ℕ | y m w = θ w}) ∈ 𝔲 :=
      (Filter.biInter_finset_mem W).mpr fun w _ => hθ w
    obtain ⟨m, hm⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem h1 h2)
    refine ⟨m, hm.1, fun w hw => ?_⟩
    have hm2 := hm.2
    simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hm2
    exact (hm2 w hw).symm
  refine ⟨θ, ?_, hagree⟩
  intro W M
  obtain ⟨m, hmM, hmagree⟩ := hagree W M
  obtain ⟨n, hnM, hn⟩ := hy m W M
  exact ⟨n, hnM, fun w hw => (hmagree w hw).trans (hn w hw)⟩

/-- **Row-agreement.** Two configurations sharing the period `k • v` that agree at the `k`
consecutive points `s • v + t • u` with `0 ≤ s < k` on a fixed row `t` agree at *every* point
`s • v + t • u` of that row.  Paper §8.4: "two fields of period `kv` that agree at `k`
consecutive lattice points of a row agree on the whole row". -/
theorem eq_on_row_of_eq_on_range {α : Type*} {y₁ y₂ : Config α} {v u : ℤ × ℤ} {k : ℕ}
    (hk : 0 < k) (hper₁ : ((k : ℤ) • v) ∈ Per y₁) (hper₂ : ((k : ℤ) • v) ∈ Per y₂) (t : ℤ)
    (hagree : ∀ s : ℤ, 0 ≤ s → s < (k : ℤ) → y₁ (s • v + t • u) = y₂ (s • v + t • u)) :
    ∀ s : ℤ, y₁ (s • v + t • u) = y₂ (s • v + t • u) := by
  intro s
  rw [G_reduce_fst hk hper₁ s t, G_reduce_fst hk hper₂ s t]
  have h1 : (0 : ℤ) ≤ ((modFin k hk s).val : ℤ) := Int.natCast_nonneg _
  have h2 : ((modFin k hk s).val : ℤ) < (k : ℤ) := by exact_mod_cast (modFin k hk s).isLt
  exact hagree _ h1 h2

/-- The finite window `{s • v + t • u : |s| ≤ W, |t| ≤ W}`, in the coordinates of a unimodular
basis `(v, u)`.  Paper §8.4: `B_W := {s v + t u : |s|, |t| ≤ W}`. -/
def BWin (v u : ℤ × ℤ) (W : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(W : ℤ)) (W : ℤ) ×ˢ Finset.Icc (-(W : ℤ)) (W : ℤ)).image
    (fun p => p.1 • v + p.2 • u)

theorem mem_BWin {v u : ℤ × ℤ} {W : ℕ} {s t : ℤ} (hs : |s| ≤ (W : ℤ)) (ht : |t| ≤ (W : ℤ)) :
    s • v + t • u ∈ BWin v u W := by
  classical
  refine Finset.mem_image.mpr ⟨(s, t), ?_, rfl⟩
  simp only [Finset.mem_product, Finset.mem_Icc]
  rw [abs_le] at hs ht
  omega

/-- **Row-agreement on a window.** If two configurations sharing the period `k • v` agree
pointwise on the window `BWin v u W` (with `W ≥ k`), they agree on every point of every row `t`
with `|t| ≤ W`, not merely on the finitely many points of that row lying in the window. Paper
§8.4: "agreement on `B_W` with `W ≥ k` implies agreement on the rows `−W` to `W`". -/
theorem eq_on_row_of_eq_on_BWin {α : Type*} {y₁ y₂ : Config α} {v u : ℤ × ℤ} {k : ℕ} (hk : 0 < k)
    (hper₁ : ((k : ℤ) • v) ∈ Per y₁) (hper₂ : ((k : ℤ) • v) ∈ Per y₂) {W : ℕ} (hWk : k ≤ W)
    {t : ℤ} (ht : |t| ≤ (W : ℤ)) (hagree : ∀ z ∈ BWin v u W, y₁ z = y₂ z) :
    ∀ s : ℤ, y₁ (s • v + t • u) = y₂ (s • v + t • u) := by
  refine eq_on_row_of_eq_on_range hk hper₁ hper₂ t (fun s hs0 hsk => hagree _ (mem_BWin ?_ ht))
  have hWZ : (k : ℤ) ≤ (W : ℤ) := by exact_mod_cast hWk
  rw [abs_le]; omega

/-- `subseqLimits G d` is invariant under `T (q • d)` for every integer `q`, not just `q = ±1`
(`T_mem_subseqLimits`/`T_neg_mem_subseqLimits` in `Nivat.Defs.Orbit`). -/
theorem T_zsmul_mem_subseqLimits {α : Type*} {G : Config α} {d : ℤ × ℤ} {y : Config α}
    (hy : y ∈ subseqLimits G d) (q : ℤ) : T (q • d) y ∈ subseqLimits G d := by
  have hpos : ∀ n : ℕ, T ((n : ℤ) • d) y ∈ subseqLimits G d := by
    intro n
    induction n with
    | zero => simpa using hy
    | succ n ih =>
      have h := T_mem_subseqLimits ih
      rw [← T_add] at h
      rwa [show d + (n : ℤ) • d = ((n + 1 : ℕ) : ℤ) • d by push_cast; ring] at h
  have hneg : ∀ n : ℕ, T ((-(n : ℤ)) • d) y ∈ subseqLimits G d := by
    intro n
    induction n with
    | zero => simpa using hy
    | succ n ih =>
      have h := T_neg_mem_subseqLimits ih
      rw [← T_add] at h
      rwa [show -d + (-(n : ℤ)) • d = (-((n + 1 : ℕ) : ℤ)) • d by push_cast; ring] at h
  rcases le_or_gt 0 q with hq | hq
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    simpa using hpos n
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (by omega : (0:ℤ) ≤ -q)
    have hqn : q = -(n : ℤ) := by omega
    rw [hqn]
    simpa using hneg n

/-- Translating a configuration does not change its period group: `T c f` and `f` have exactly
the same periods.  (Needed because Step 1b repeatedly shifts a limit config by `q • d` to move a
"bad row" into a fixed window, and this must not disturb the known period `k • v`.) -/
theorem Per_T {α : Type*} (f : Config α) (c u : ℤ × ℤ) : u ∈ Per (T c f) ↔ u ∈ Per f := by
  simp only [mem_Per_iff]
  constructor
  · intro h
    funext z
    have h' := congrFun h (z - c)
    simp only [T_apply] at h'
    rwa [show z - c + u + c = z + u from by abel, show z - c + c = z from by abel] at h'
  · intro h
    funext z
    show (T c f) (z + u) = (T c f) z
    simp only [T_apply]
    rw [show z + u + c = z + c + u from by abel]
    exact congrFun h (z + c)

/-- **Pigeonhole for `ℕ` into a finite type.** Any `f : ℕ → β` with `β` finite has some fiber
that is infinite. Used to find a single point `z ∈ F` (the finite window of §8.4) that is the
"reduced bad point" for infinitely many terms of a sequence. -/
theorem exists_infinite_fiber {β : Type*} [Finite β] (f : ℕ → β) :
    ∃ b, {n : ℕ | f n = b}.Infinite := by
  by_contra h
  push Not at h
  have heq : (Set.univ : Set ℕ) = ⋃ b : β, {n : ℕ | f n = b} := by
    ext n; simp
  have hfin : (Set.univ : Set ℕ).Finite := by
    rw [heq]; exact Set.finite_iUnion h
  exact Set.infinite_univ hfin

/-- An infinite set of naturals can be enumerated by a strictly increasing sequence landing
inside it, with `n ≤ enum S h n`; in particular `enum S h n → ∞`, so it can be used to pick
"arbitrarily late" indices from an infinite index set. -/
noncomputable def enumInfinite (S : Set ℕ) (_h : S.Infinite) : ℕ → ℕ := Nat.nth (· ∈ S)

theorem enumInfinite_mem (S : Set ℕ) (h : S.Infinite) (n : ℕ) : enumInfinite S h n ∈ S :=
  Nat.nth_mem_of_infinite h n

theorem le_enumInfinite (S : Set ℕ) (h : S.Infinite) (n : ℕ) : n ≤ enumInfinite S h n :=
  (Nat.nth_strictMono h).le_apply

/-- **Bad-row dichotomy.** Given that `ϖ` is a known period of `y` for every row in `[-n, n-P₀]`,
either `ϖ ∈ Per y` outright (the "no bad row" case, which combined with an upper bound on
`Tr(y)` gives an immediate contradiction downstream), or there is a *bad row* `x` strictly
outside `[-n, n-P₀]` on one side, extremal in the sense that every row strictly between `x` and
the known-good window is also good. This is the per-`n` core of paper §8.4 Lemma 8.16 Step 1,
made bilateral (the paper only writes the left case and calls the right "symmetric"). -/
theorem exists_bad_row_or_good {α : Type*} {y : Config α} {v ϖ : ℤ × ℤ} {P₀ n : ℤ}
    (hnP : -n ≤ n - P₀)
    (hknown : ∀ t : ℤ, -n ≤ t → t ≤ n - P₀ → ∀ z, pi v z = t → y (z + ϖ) = y z) :
    (∀ z, y (z + ϖ) = y z) ∨
    (∃ x : ℤ, x < -n ∧ (∃ z, pi v z = x ∧ y (z + ϖ) ≠ y z) ∧
       ∀ t : ℤ, x < t → t ≤ n - P₀ → ∀ z, pi v z = t → y (z + ϖ) = y z) ∨
    (∃ x : ℤ, n - P₀ < x ∧ (∃ z, pi v z = x ∧ y (z + ϖ) ≠ y z) ∧
       ∀ t : ℤ, n - P₀ ≤ t → t < x → ∀ z, pi v z = t → y (z + ϖ) = y z) := by
  by_cases hall : ∀ z, y (z + ϖ) = y z
  · exact Or.inl hall
  · push Not at hall
    obtain ⟨z0, hz0⟩ := hall
    set t0 : ℤ := pi v z0 with ht0
    by_cases hmid : -n ≤ t0 ∧ t0 ≤ n - P₀
    · exact absurd (hknown t0 hmid.1 hmid.2 z0 rfl) hz0
    · rw [not_and_or, not_le, not_le] at hmid
      rcases hmid with hlt | hgt
      · right; left
        have hne : ∃ t : ℤ, t < -n ∧ ∃ z, pi v z = t ∧ y (z + ϖ) ≠ y z :=
          ⟨t0, hlt, z0, rfl, hz0⟩
        obtain ⟨x, ⟨hxlt, z, hzx, hzbad⟩, hxub⟩ :=
          Int.exists_greatest_of_bdd (P := fun t => t < -n ∧ ∃ z, pi v z = t ∧ y (z + ϖ) ≠ y z)
            ⟨-n - 1, fun t ht => by omega⟩ hne
        refine ⟨x, hxlt, ⟨z, hzx, hzbad⟩, fun t hxt htn z' hz' => ?_⟩
        by_contra hbad
        rcases lt_or_ge t (-n) with ht | ht
        · exact absurd (hxub t ⟨ht, z', hz', hbad⟩) (by omega)
        · exact hbad (hknown t ht htn z' hz')
      · right; right
        have hne : ∃ t : ℤ, n - P₀ < t ∧ ∃ z, pi v z = t ∧ y (z + ϖ) ≠ y z :=
          ⟨t0, hgt, z0, rfl, hz0⟩
        obtain ⟨x, ⟨hxgt, z, hzx, hzbad⟩, hxlb⟩ :=
          Int.exists_least_of_bdd (P := fun t => n - P₀ < t ∧ ∃ z, pi v z = t ∧ y (z + ϖ) ≠ y z)
            ⟨n - P₀ + 1, fun t ht => by omega⟩ hne
        refine ⟨x, hxgt, ⟨z, hzx, hzbad⟩, fun t htn hxt z' hz' => ?_⟩
        by_contra hbad
        rcases lt_or_ge (n - P₀) t with ht | ht
        · exact absurd (hxlb t ⟨ht, z', hz', hbad⟩) (by omega)
        · exact hbad (hknown t (by omega) ht z' hz')

/-- **Shift into a fixed range.** Translating by `q := ⌈-x/δ⌉` (via `T (q • d)`, where
`δ := -(pi v d) > 0`) moves a bad row at `x` to a fixed row `r ∈ [0, δ)`, and moves a known-good
interval `(x, M]` to `(r, M + q • δ]` — both computed via the period-independent identity
`pi v (z + q • d) = pi v z + q * pi v d`. This is the "reduce the bad row mod `δ`" step of
paper §8.4 Lemma 8.16 Step 1, stated so it applies verbatim on either side of the bilateral
dichotomy (`x` far left of the known-good window, or far right of it). -/
theorem shift_bad_and_good {α : Type*} {y : Config α} {v ϖ d : ℤ × ℤ} {δ : ℤ} (hδ : pi v d = -δ)
    (hδpos : 0 < δ) (x : ℤ) :
    let q : ℤ := -(x / δ)
    let r : ℤ := x % δ
    let y' : Config α := T (q • d) y
    (0 ≤ r ∧ r < δ) ∧
    ((∃ z, pi v z = x ∧ y (z + ϖ) ≠ y z) → ∃ z', pi v z' = r ∧ y' (z' + ϖ) ≠ y' z') ∧
    (∀ M : ℤ, (∀ t : ℤ, x < t → t ≤ M → ∀ z, pi v z = t → y (z + ϖ) = y z) →
      ∀ t' : ℤ, r < t' → t' ≤ M + q * δ → ∀ z', pi v z' = t' → y' (z' + ϖ) = y' z') := by
  intro q r y'
  have hxqr : x + q * δ = r := by
    have h1 := Int.mul_ediv_add_emod x δ
    show x + (-(x / δ)) * δ = x % δ
    linear_combination -h1
  refine ⟨⟨Int.emod_nonneg x (by omega), Int.emod_lt_of_pos x hδpos⟩, ?_, ?_⟩
  · rintro ⟨z, hz, hzbad⟩
    refine ⟨z - q • d, ?_, ?_⟩
    · have hcalc : pi v (z - q • d) = pi v z - q * pi v d := by
        rw [pi_sub, pi_smul]
      rw [hcalc, hz, hδ]
      linear_combination hxqr
    · have e1 : z - q • d + q • d = z := by abel
      have e2 : z - q • d + ϖ + q • d = z + ϖ := by abel
      show y' (z - q • d + ϖ) ≠ y' (z - q • d)
      show y (z - q • d + ϖ + q • d) ≠ y (z - q • d + q • d)
      rw [e1, e2]
      exact hzbad
  · intro M hgood t' ht' ht'M z' hz'
    set z : ℤ × ℤ := z' + q • d with hzdef
    have hpiz : pi v z = t' - q * δ := by
      have hcalc : pi v z = pi v z' + q * pi v d := by
        rw [hzdef, pi_add, pi_smul]
      rw [hcalc, hz', hδ]; ring
    have hxz : x < t' - q * δ := by omega
    have hzM : t' - q * δ ≤ M := by omega
    have hfin := hgood (t' - q * δ) hxz hzM z hpiz
    show y' (z' + ϖ) = y' z'
    show y (z' + ϖ + q • d) = y (z' + q • d)
    rw [show z' + ϖ + q • d = z + ϖ from by rw [hzdef]; abel]
    rw [show z' + q • d = z from rfl]
    exact hfin

/-- Mirror of `shift_bad_and_good` for a known-good interval *below* the bad row `x` (the
right-hand branch of the bilateral dichotomy `exists_bad_row_or_good`). The shift `q`, residue
`r` and shifted configuration `y'` are defined by the exact same formulas as in
`shift_bad_and_good` — `q := -(x / δ)`, `r := x % δ` — since these already produce a *negative*
`q` automatically when `x` is large and positive, sliding it down to `r ∈ [0, δ)`; only the
direction of the transported "known-good" hypothesis is flipped (`M ≤ t < x` becomes
`M + qδ ≤ t' < r`, instead of `x < t ≤ M` becoming `r < t' ≤ M + qδ`). -/
theorem shift_bad_and_good_right {α : Type*} {y : Config α} {v ϖ d : ℤ × ℤ} {δ : ℤ}
    (hδ : pi v d = -δ) (hδpos : 0 < δ) (x : ℤ) :
    let q : ℤ := -(x / δ)
    let r : ℤ := x % δ
    let y' : Config α := T (q • d) y
    (0 ≤ r ∧ r < δ) ∧
    ((∃ z, pi v z = x ∧ y (z + ϖ) ≠ y z) → ∃ z', pi v z' = r ∧ y' (z' + ϖ) ≠ y' z') ∧
    (∀ M : ℤ, (∀ t : ℤ, M ≤ t → t < x → ∀ z, pi v z = t → y (z + ϖ) = y z) →
      ∀ t' : ℤ, M + q * δ ≤ t' → t' < r → ∀ z', pi v z' = t' → y' (z' + ϖ) = y' z') := by
  intro q r y'
  have hxqr : x + q * δ = r := by
    have h1 := Int.mul_ediv_add_emod x δ
    show x + (-(x / δ)) * δ = x % δ
    linear_combination -h1
  refine ⟨⟨Int.emod_nonneg x (by omega), Int.emod_lt_of_pos x hδpos⟩, ?_, ?_⟩
  · rintro ⟨z, hz, hzbad⟩
    refine ⟨z - q • d, ?_, ?_⟩
    · have hcalc : pi v (z - q • d) = pi v z - q * pi v d := by
        rw [pi_sub, pi_smul]
      rw [hcalc, hz, hδ]
      linear_combination hxqr
    · have e1 : z - q • d + q • d = z := by abel
      have e2 : z - q • d + ϖ + q • d = z + ϖ := by abel
      show y' (z - q • d + ϖ) ≠ y' (z - q • d)
      show y (z - q • d + ϖ + q • d) ≠ y (z - q • d + q • d)
      rw [e1, e2]
      exact hzbad
  · intro M hgood t' ht' ht'M z' hz'
    set z : ℤ × ℤ := z' + q • d with hzdef
    have hpiz : pi v z = t' - q * δ := by
      have hcalc : pi v z = pi v z' + q * pi v d := by
        rw [hzdef, pi_add, pi_smul]
      rw [hcalc, hz', hδ]; ring
    have hxz : M ≤ t' - q * δ := by omega
    have hzM : t' - q * δ < x := by omega
    have hfin := hgood (t' - q * δ) hxz hzM z hpiz
    show y' (z' + ϖ) = y' z'
    show y (z' + ϖ + q • d) = y (z' + q • d)
    rw [show z' + ϖ + q • d = z + ϖ from by rw [hzdef]; abel]
    rw [show z' + q • d = z from rfl]
    exact hfin

theorem Per.apply_of_sub {α : Type*} {y : Config α} {a b : ℤ × ℤ} (h : a - b ∈ Per y) (c : ℤ × ℤ) :
    y (a + c) = y (b + c) := by
  have := Per.apply h (b + c)
  rwa [show b + c + (a - b) = a + c from by abel] at this

theorem reduce_bad_to_window {α : Type*} {y' : Config α} {v u ϖ : ℤ × ℤ} (hvu : det v u = 1)
    {k : ℕ} (hk : 0 < k) (hper : ((k : ℤ) • v) ∈ Per y') {z' : ℤ × ℤ} {r : ℤ} (hz' : pi v z' = r)
    (hbad : y' (z' + ϖ) ≠ y' z') :
    y' (((modFin k hk (det z' u) : Fin k).val : ℤ) • v + r • u + ϖ) ≠
      y' (((modFin k hk (det z' u) : Fin k).val : ℤ) • v + r • u) := by
  set s : ℤ := det z' u with hs
  have hzdecomp : z' = s • v + r • u := by
    rw [← hz']; exact eq_smul_add_smul hvu z'
  set s' : ℤ := ((modFin k hk s).val : ℤ) with hs'
  set z'' : ℤ × ℤ := s' • v + r • u with hz''
  have hsub : z' - z'' = (s - s') • v := by
    rw [hzdecomp, hz'']
    have : s • v + r • u - (s' • v + r • u) = (s - s') • v := by
      rw [sub_smul]; abel
    exact this
  have hmulk : ∃ N : ℤ, s - s' = (k : ℤ) * N := by
    have hval : s' = s % (k : ℤ) := by rw [hs']; exact modFin_val k hk s
    refine ⟨s / (k : ℤ), ?_⟩
    have heuc := Int.mul_ediv_add_emod s (k : ℤ)
    rw [hval]; linear_combination -heuc
  obtain ⟨N, hN⟩ := hmulk
  have hmem : z' - z'' ∈ Per y' := by
    rw [hsub, hN, show ((k : ℤ) * N) • v = N • ((k : ℤ) • v) from by rw [mul_comm, mul_smul]]
    exact AddSubgroup.zsmul_mem _ hper N
  have h1 := Per.apply_of_sub hmem (0 : ℤ × ℤ)
  have h2 := Per.apply_of_sub hmem ϖ
  simp only [add_zero] at h1
  rw [h1, h2] at hbad
  exact hbad

/-- **Step 1b, left-bad-row branch.** One half of the bilateral case split of paper §8.4
Lemma 8.16 Step 1: if `y : ℕ → Ω` (`Ω := subseqLimits G d`) is a sequence witnessed to
diagonally agree with a fixed doubly periodic `θ ∈ Ω` (via `hmagree`, the output of
`exists_mem_subseqLimits_agree` applied to `y`) on ever-larger windows `BWin v u (N n)`, and for
infinitely many `n ∈ S` the comparison of `y (m n)` against `θ`'s witnessing period `ϖ`
(`pi v ϖ = Tr(θ) > 0`) has its extremal bad row strictly to the *left* of `-(N n)` (i.e. case 2
of `exists_bad_row_or_good`), then a contradiction follows.

Proof sketch: shift each bad row to a fixed residue in `[0, δ)` (`shift_bad_and_good`,
`δ := -(pi v d)`), reduce its `v`-coefficient mod `k` (`reduce_bad_to_window`), and pigeonhole
(`exists_infinite_fiber`) over the finite window `Fin k × Fin δ.toNat` to find a single point
`z*` that is a "bad point" (witnessing `y' j (z*+ϖ) ≠ y' j z*` for the shifted configuration
`y' j`) for infinitely many `j` in a further index set `J`.  A second application of
`exists_mem_subseqLimits_agree` to `(y' j)_{j ∈ J}` (reindexed via `enumInfinite`) extracts a
doubly periodic `ψ ∈ Ω` that inherits the bad inequality at `z*` exactly (from a single window
comparison), together with, for any single row strictly above `z*`'s, the "goodness" fact at
that row (re-derived per use from `hgood`, since the good interval `(r, M + qδ]` widens without
bound down that branch's index).  Taking `λ ∈ Per ψ` with `pi v λ = Tr(ψ) > 0`
(`exists_mem_Per_pi_eq_trace`), the row of `z* + λ` is safely inside the inherited good zone, so
`ψ (z* + λ + ϖ) = ψ (z* + λ)`; combined with `λ ∈ Per ψ` (applied at `z*` and at `z* + ϖ`) this
gives `ψ (z* + ϖ) = ψ z*`, contradicting the inherited bad inequality.

This is a genuinely one-sided argument: it uses `0 < pi v ϖ` essentially, to ensure the shift by
`ϖ` (from a good row) and by `λ` (from `z*`) both move in the *same* (increasing) direction along
`pi v`; the mirror-image "right bad row" branch needs the opposite sign and does not reduce to
this one by relabelling `ϖ ↦ -ϖ` alone, since the *known-good* interval also flips which side of
the bad row it lies on. -/
theorem false_of_infinite_left_bad_row {α : Type*} [Finite α] {G : Config α}
    {v u d : ℤ × ℤ} (hvu : det v u = 1) {k : ℕ} (hk : 0 < k) (hd : 0 < -(pi v d))
    (hlim : ∀ y ∈ subseqLimits G d, DoublyPeriodic y)
    (y : ℕ → Config α) (hy : ∀ n, y n ∈ subseqLimits G d)
    (hyper : ∀ n, ((k : ℤ) • v) ∈ Per (y n))
    {θ : Config α} (_hθΩ : θ ∈ subseqLimits G d) (_hθper : ((k : ℤ) • v) ∈ Per θ)
    {ϖ : ℤ × ℤ} (_hϖper : ϖ ∈ Per θ) (hϖpos : 0 < pi v ϖ)
    {N : ℕ → ℕ} (hNmono : ∀ n, n ≤ N n)
    {m : ℕ → ℕ} (_hmagree : ∀ n, ∀ w ∈ BWin v u (N n), θ w = y (m n) w)
    {S : Set ℕ} (hS : S.Infinite)
    (hbad : ∀ n ∈ S, ∃ x : ℤ, x < -(N n : ℤ) ∧
      (∃ z, pi v z = x ∧ y (m n) (z + ϖ) ≠ y (m n) z) ∧
      ∀ t : ℤ, x < t → t ≤ (N n : ℤ) - pi v ϖ → ∀ z, pi v z = t →
        y (m n) (z + ϖ) = y (m n) z) :
    False := by
  classical
  set δ : ℤ := -(pi v d) with hδdef
  have hδeq : pi v d = -δ := by omega
  have hδpos : 0 < δ := hd
  have hδnatpos : 0 < δ.toNat := by omega
  -- Enumerate `S` and unpack the case-2 data along it.
  set e : ℕ → ℕ := enumInfinite S hS with hedef
  have he_mem : ∀ j, e j ∈ S := enumInfinite_mem S hS
  have he_mono : ∀ j, j ≤ e j := le_enumInfinite S hS
  have hbad' : ∀ j : ℕ, ∃ x : ℤ, x < -(N (e j) : ℤ) ∧
      (∃ z, pi v z = x ∧ y (m (e j)) (z + ϖ) ≠ y (m (e j)) z) ∧
      ∀ t : ℤ, x < t → t ≤ (N (e j) : ℤ) - pi v ϖ → ∀ z, pi v z = t →
        y (m (e j)) (z + ϖ) = y (m (e j)) z :=
    fun j => hbad (e j) (he_mem j)
  choose x hxlt hbadex hgood using hbad'
  choose z0 hz0pi hz0bad using hbadex
  -- Shift the bad row at `x j` to a fixed residue `r j ∈ [0, δ)`.
  set q : ℕ → ℤ := fun j => -(x j / δ) with hqdef
  set r : ℕ → ℤ := fun j => x j % δ with hrdef
  set y' : ℕ → Config α := fun j => T ((q j) • d) (y (m (e j))) with hy'def
  have hshift : ∀ j, (0 ≤ r j ∧ r j < δ) ∧
      ((∃ z, pi v z = x j ∧ y (m (e j)) (z + ϖ) ≠ y (m (e j)) z) →
        ∃ z', pi v z' = r j ∧ y' j (z' + ϖ) ≠ y' j z') ∧
      (∀ M : ℤ, (∀ t, x j < t → t ≤ M → ∀ z, pi v z = t →
          y (m (e j)) (z + ϖ) = y (m (e j)) z) →
        ∀ t', r j < t' → t' ≤ M + (q j) * δ → ∀ z', pi v z' = t' →
          y' j (z' + ϖ) = y' j z') :=
    fun j => shift_bad_and_good hδeq hδpos (x j)
  have hbad2 : ∀ j, ∃ z', pi v z' = r j ∧ y' j (z' + ϖ) ≠ y' j z' :=
    fun j => (hshift j).2.1 ⟨z0 j, hz0pi j, hz0bad j⟩
  choose z1 hz1pi hz1bad using hbad2
  have hgood2 : ∀ j, ∀ t', r j < t' → t' ≤ ((N (e j) : ℤ) - pi v ϖ) + (q j) * δ →
      ∀ z', pi v z' = t' → y' j (z' + ϖ) = y' j z' :=
    fun j => (hshift j).2.2 ((N (e j) : ℤ) - pi v ϖ) (hgood j)
  have hy'per : ∀ j, ((k : ℤ) • v) ∈ Per (y' j) :=
    fun j => (Per_T (y (m (e j))) ((q j) • d) ((k : ℤ) • v)).mpr (hyper (m (e j)))
  have hy'Ω : ∀ j, y' j ∈ subseqLimits G d :=
    fun j => T_zsmul_mem_subseqLimits (hy (m (e j))) (q j)
  -- Reduce the shifted bad point's `v`-coefficient mod `k`.
  have hreduce : ∀ j, y' j (((modFin k hk (det (z1 j) u)).val : ℤ) • v + (r j) • u + ϖ) ≠
      y' j (((modFin k hk (det (z1 j) u)).val : ℤ) • v + (r j) • u) :=
    fun j => reduce_bad_to_window hvu hk (hy'per j) (hz1pi j) (hz1bad j)
  -- Pigeonhole over the finite window `Fin k × Fin δ.toNat`.
  set F : ℕ → Fin k × Fin δ.toNat :=
    fun j => (modFin k hk (det (z1 j) u), modFin δ.toNat hδnatpos (r j)) with hFdef
  obtain ⟨b, hJ⟩ := exists_infinite_fiber F
  set J : Set ℕ := {j | F j = b} with hJdef
  have hrval : ∀ j, ((modFin δ.toNat hδnatpos (r j)).val : ℤ) = r j := by
    intro j
    have h1 := modFin_val δ.toNat hδnatpos (r j)
    have h2 : (δ.toNat : ℤ) = δ := Int.toNat_of_nonneg hδpos.le
    rw [h1, h2, Int.emod_eq_of_lt (hshift j).1.1 (hshift j).1.2]
  set zstar : ℤ × ℤ := (b.1.val : ℤ) • v + (b.2.val : ℤ) • u with hzstardef
  have hzeq : ∀ j ∈ J, ((modFin k hk (det (z1 j) u)).val : ℤ) • v + (r j) • u = zstar := by
    intro j hj
    have hFeq : F j = b := hj
    have h1 : modFin k hk (det (z1 j) u) = b.1 := congrArg Prod.fst hFeq
    have h2 : modFin δ.toNat hδnatpos (r j) = b.2 := congrArg Prod.snd hFeq
    rw [h1, hzstardef, ← hrval j, h2]
  have hstarbad : ∀ j ∈ J, y' j (zstar + ϖ) ≠ y' j zstar := by
    intro j hj
    rw [← hzeq j hj]
    exact hreduce j
  -- Second diagonal extraction, along the (reindexed) infinite fiber `J`.
  have hJinf : J.Infinite := hJ
  set g : ℕ → ℕ := enumInfinite J hJinf with hgdef
  have hg_mem : ∀ i, g i ∈ J := enumInfinite_mem J hJinf
  have hg_mono : ∀ i, i ≤ g i := le_enumInfinite J hJinf
  set w : ℕ → Config α := fun i => y' (g i) with hwdef
  have hwΩ : ∀ i, w i ∈ subseqLimits G d := fun i => hy'Ω (g i)
  obtain ⟨ψ, hψΩ, hψagree⟩ := exists_mem_subseqLimits_agree w hwΩ
  have hψdp : DoublyPeriodic ψ := hlim ψ hψΩ
  -- `ψ` inherits the bad inequality at `zstar` from a single window comparison.
  have hψbad : ψ (zstar + ϖ) ≠ ψ zstar := by
    obtain ⟨i, -, hi⟩ := hψagree {zstar, zstar + ϖ} 0
    have h1 : ψ zstar = w i zstar := hi zstar (by simp)
    have h2 : ψ (zstar + ϖ) = w i (zstar + ϖ) := hi (zstar + ϖ) (by simp)
    rw [h1, h2]
    exact hstarbad (g i) (hg_mem i)
  -- Take a period `λ` of `ψ` with `pi v λ = Tr(ψ) > 0`.
  have hv : Primitive v := Primitive_of_det_eq_one hvu
  obtain ⟨lam, hlamper, hlameq⟩ := exists_mem_Per_pi_eq_trace hv hψdp
  have hlampos : 0 < pi v lam := by rw [hlameq]; exact_mod_cast trace_pos hv hψdp
  -- Goodness at the row of `zstar + lam`, re-derived from `hgood2` for a large enough index.
  have hψgood : ψ ((zstar + lam) + ϖ) = ψ (zstar + lam) := by
    have hthresh : ∃ M0 : ℕ, ∀ i, M0 ≤ i →
        (r (g i) < pi v zstar + pi v lam) ∧
        (pi v zstar + pi v lam ≤ ((N (e (g i)) : ℤ) - pi v ϖ) + (q (g i)) * δ) := by
      -- `r (g i) = pi v zstar` exactly (from the pigeonhole fiber membership), and the bound
      -- `M (g i) + q (g i) δ` grows without bound in `i`.
      have hrstar : ∀ j ∈ J, r j = pi v zstar := by
        intro j hj
        have hFeq : F j = b := hj
        have h2 : modFin δ.toNat hδnatpos (r j) = b.2 := congrArg Prod.snd hFeq
        rw [hzstardef, pi_add, pi_smul, pi_smul]
        have hpivv : pi v v = 0 := det_self v
        have hpivu : pi v u = 1 := hvu
        rw [hpivv, hpivu]
        rw [← hrval j, h2]
        ring
      refine ⟨(pi v ϖ + pi v lam).toNat + 1, fun i hi => ?_⟩
      have hrgi : r (g i) = pi v zstar := hrstar (g i) (hg_mem i)
      have hxlt_gi := hxlt (g i)
      have hNgi : (i : ℤ) ≤ (N (e (g i)) : ℤ) := by
        have h1 : i ≤ g i := hg_mono i
        have h2 : g i ≤ e (g i) := he_mono (g i)
        have h3 : e (g i) ≤ N (e (g i)) := hNmono (e (g i))
        exact_mod_cast (h1.trans h2).trans h3
      constructor
      · rw [hrgi]; omega
      · have hqr_gi : x (g i) + (q (g i)) * δ = r (g i) := by
          have h1 := Int.mul_ediv_add_emod (x (g i)) δ
          show x (g i) + (-(x (g i) / δ)) * δ = x (g i) % δ
          linear_combination -h1
        have hqd : (q (g i)) * δ = r (g i) - x (g i) := by omega
        rw [hqd, hrgi]
        omega
    -- Use `hthresh` to extract a window instance witnessing goodness at the row of `zstar + lam`.
    obtain ⟨M0, hM0⟩ := hthresh
    obtain ⟨i, hiM0, hiagree⟩ :=
      hψagree ({zstar + lam, zstar + lam + ϖ} : Finset (ℤ × ℤ)) M0
    have h1 : ψ (zstar + lam) = w i (zstar + lam) := hiagree _ (by simp)
    have h2 : ψ (zstar + lam + ϖ) = w i (zstar + lam + ϖ) := hiagree _ (by simp)
    have hzeq2 : pi v (zstar + lam) = pi v zstar + pi v lam := pi_add v zstar lam
    have hgi := hM0 i hiM0
    have hgoodinst : y' (g i) ((zstar + lam) + ϖ) = y' (g i) (zstar + lam) :=
      hgood2 (g i) (pi v zstar + pi v lam) hgi.1 hgi.2 (zstar + lam) hzeq2
    rw [h2, h1]
    exact hgoodinst
  -- Combine `hψgood` with `lam ∈ Per ψ` to contradict `hψbad`.
  have hcombine : ψ (zstar + ϖ) = ψ zstar := by
    have e1 : ψ ((zstar + lam) + ϖ) = ψ (zstar + ϖ) := by
      have hraw := Per.apply hlamper (zstar + ϖ)
      have heq : (zstar + ϖ) + lam = (zstar + lam) + ϖ := by abel
      rwa [heq] at hraw
    rw [← e1, hψgood]
    exact Per.apply hlamper zstar
  exact hψbad hcombine

/-- **Step 1b, right-bad-row branch.** Mirror of `false_of_infinite_left_bad_row`: case 3 of
`exists_bad_row_or_good` (the extremal bad row is strictly *above* the known-good window) occurs
for infinitely many `n ∈ S`.

Departure from a literal mirror, worth recording: `exists_bad_row_or_good`'s case-3 conclusion by
itself only extends goodness up from `(N n) - pi v ϖ` (the *near* edge of the originally-known
window `[-(N n), (N n) - pi v ϖ]`), not from `-(N n)` (the *far* edge). Combining that conclusion
with the window's own `hknown` hypothesis (still available to whoever derives `hbad`, since
`exists_bad_row_or_good` doesn't consume it) recovers goodness all the way down from `-(N n)`, and
*that* stronger fact is what `hbad` below assumes. This combination costs nothing at the call
site (`hknown` and the case-3 disjunct just get glued with an `if`/`by_cases` on `t ≤ (N n) - pi v
ϖ`), but it is essential here: with only the case-3 disjunct's own near edge, the shifted
good-interval's floor `-(N n) + q·δ` need not tend to `-∞` (both `N n` and the bad row `x` can grow
at the same rate, so their difference need not grow), which would strand the pigeonholed
argument below. With the far edge `-(N n)` in hand instead, the floor is `-(N n) + q·δ =
-(N n) + r - x ≤ -(N n) + r` (since `x ≥ 0` eventually), which does tend to `-∞` as `N n → ∞`,
exactly parallel to the left branch's use of `(N n) - pi v ϖ` (there, the *far* edge from the
left bad row's perspective).

Downstream of that fix, the argument is the literal mirror of the left branch: shift the bad row
to `r ∈ [0, δ)` via the same `q := -(x/δ)` formula (which already produces a negative `q`
automatically once `x` is large positive, so no separate `T^{-qd}` branch is needed in this
formalisation — `shift_bad_and_good_right` is `shift_bad_and_good` with the transported
known-good hypothesis flipped from `x < t ≤ M` to `M ≤ t < x`), pigeonhole to a single bad point
`z*`, extract a second doubly periodic `ψ`, and take `λ ∈ Per ψ` with `pi v λ = Tr(ψ) > 0`; now
`z* - λ` (not `z* + λ`) sits safely in the good zone below `z*`, giving
`ψ (z* - λ + ϖ) = ψ (z* - λ)`, and combined with `λ ∈ Per ψ` (applied at `z* - λ` and at
`z* - λ + ϖ`) this again gives `ψ (z* + ϖ) = ψ z*`, contradicting the inherited bad inequality. -/
theorem false_of_infinite_right_bad_row {α : Type*} [Finite α] {G : Config α}
    {v u d : ℤ × ℤ} (hvu : det v u = 1) {k : ℕ} (hk : 0 < k) (hd : 0 < -(pi v d))
    (hlim : ∀ y ∈ subseqLimits G d, DoublyPeriodic y)
    (y : ℕ → Config α) (hy : ∀ n, y n ∈ subseqLimits G d)
    (hyper : ∀ n, ((k : ℤ) • v) ∈ Per (y n))
    {ϖ : ℤ × ℤ} (hϖpos : 0 < pi v ϖ)
    {N : ℕ → ℕ} (hNmono : ∀ n, n ≤ N n)
    {m : ℕ → ℕ}
    {S : Set ℕ} (hS : S.Infinite)
    (hbad : ∀ n ∈ S, ∃ x : ℤ, (N n : ℤ) - pi v ϖ < x ∧
      (∃ z, pi v z = x ∧ y (m n) (z + ϖ) ≠ y (m n) z) ∧
      ∀ t : ℤ, -(N n : ℤ) ≤ t → t < x → ∀ z, pi v z = t →
        y (m n) (z + ϖ) = y (m n) z) :
    False := by
  classical
  set δ : ℤ := -(pi v d) with hδdef
  have hδeq : pi v d = -δ := by omega
  have hδpos : 0 < δ := hd
  have hδnatpos : 0 < δ.toNat := by omega
  -- Enumerate `S` and unpack the case-3 data along it.
  set e : ℕ → ℕ := enumInfinite S hS with hedef
  have he_mem : ∀ j, e j ∈ S := enumInfinite_mem S hS
  have he_mono : ∀ j, j ≤ e j := le_enumInfinite S hS
  have hbad' : ∀ j : ℕ, ∃ x : ℤ, (N (e j) : ℤ) - pi v ϖ < x ∧
      (∃ z, pi v z = x ∧ y (m (e j)) (z + ϖ) ≠ y (m (e j)) z) ∧
      ∀ t : ℤ, -(N (e j) : ℤ) ≤ t → t < x → ∀ z, pi v z = t →
        y (m (e j)) (z + ϖ) = y (m (e j)) z :=
    fun j => hbad (e j) (he_mem j)
  choose x hxgt hbadex hgood using hbad'
  choose z0 hz0pi hz0bad using hbadex
  -- Shift the bad row at `x j` to a fixed residue `r j ∈ [0, δ)`.
  set q : ℕ → ℤ := fun j => -(x j / δ) with hqdef
  set r : ℕ → ℤ := fun j => x j % δ with hrdef
  set y' : ℕ → Config α := fun j => T ((q j) • d) (y (m (e j))) with hy'def
  have hshift : ∀ j, (0 ≤ r j ∧ r j < δ) ∧
      ((∃ z, pi v z = x j ∧ y (m (e j)) (z + ϖ) ≠ y (m (e j)) z) →
        ∃ z', pi v z' = r j ∧ y' j (z' + ϖ) ≠ y' j z') ∧
      (∀ M : ℤ, (∀ t : ℤ, M ≤ t → t < x j → ∀ z, pi v z = t →
          y (m (e j)) (z + ϖ) = y (m (e j)) z) →
        ∀ t', M + (q j) * δ ≤ t' → t' < r j → ∀ z', pi v z' = t' →
          y' j (z' + ϖ) = y' j z') :=
    fun j => shift_bad_and_good_right hδeq hδpos (x j)
  have hbad2 : ∀ j, ∃ z', pi v z' = r j ∧ y' j (z' + ϖ) ≠ y' j z' :=
    fun j => (hshift j).2.1 ⟨z0 j, hz0pi j, hz0bad j⟩
  choose z1 hz1pi hz1bad using hbad2
  have hgood2 : ∀ j, ∀ t', -(N (e j) : ℤ) + (q j) * δ ≤ t' → t' < r j →
      ∀ z', pi v z' = t' → y' j (z' + ϖ) = y' j z' :=
    fun j => (hshift j).2.2 (-(N (e j) : ℤ)) (hgood j)
  have hy'per : ∀ j, ((k : ℤ) • v) ∈ Per (y' j) :=
    fun j => (Per_T (y (m (e j))) ((q j) • d) ((k : ℤ) • v)).mpr (hyper (m (e j)))
  have hy'Ω : ∀ j, y' j ∈ subseqLimits G d :=
    fun j => T_zsmul_mem_subseqLimits (hy (m (e j))) (q j)
  -- Reduce the shifted bad point's `v`-coefficient mod `k`.
  have hreduce : ∀ j, y' j (((modFin k hk (det (z1 j) u)).val : ℤ) • v + (r j) • u + ϖ) ≠
      y' j (((modFin k hk (det (z1 j) u)).val : ℤ) • v + (r j) • u) :=
    fun j => reduce_bad_to_window hvu hk (hy'per j) (hz1pi j) (hz1bad j)
  -- Pigeonhole over the finite window `Fin k × Fin δ.toNat`.
  set F : ℕ → Fin k × Fin δ.toNat :=
    fun j => (modFin k hk (det (z1 j) u), modFin δ.toNat hδnatpos (r j)) with hFdef
  obtain ⟨b, hJ⟩ := exists_infinite_fiber F
  set J : Set ℕ := {j | F j = b} with hJdef
  have hrval : ∀ j, ((modFin δ.toNat hδnatpos (r j)).val : ℤ) = r j := by
    intro j
    have h1 := modFin_val δ.toNat hδnatpos (r j)
    have h2 : (δ.toNat : ℤ) = δ := Int.toNat_of_nonneg hδpos.le
    rw [h1, h2, Int.emod_eq_of_lt (hshift j).1.1 (hshift j).1.2]
  set zstar : ℤ × ℤ := (b.1.val : ℤ) • v + (b.2.val : ℤ) • u with hzstardef
  have hzeq : ∀ j ∈ J, ((modFin k hk (det (z1 j) u)).val : ℤ) • v + (r j) • u = zstar := by
    intro j hj
    have hFeq : F j = b := hj
    have h1 : modFin k hk (det (z1 j) u) = b.1 := congrArg Prod.fst hFeq
    have h2 : modFin δ.toNat hδnatpos (r j) = b.2 := congrArg Prod.snd hFeq
    rw [h1, hzstardef, ← hrval j, h2]
  have hstarbad : ∀ j ∈ J, y' j (zstar + ϖ) ≠ y' j zstar := by
    intro j hj
    rw [← hzeq j hj]
    exact hreduce j
  -- Second diagonal extraction, along the (reindexed) infinite fiber `J`.
  have hJinf : J.Infinite := hJ
  set g : ℕ → ℕ := enumInfinite J hJinf with hgdef
  have hg_mem : ∀ i, g i ∈ J := enumInfinite_mem J hJinf
  have hg_mono : ∀ i, i ≤ g i := le_enumInfinite J hJinf
  set w : ℕ → Config α := fun i => y' (g i) with hwdef
  have hwΩ : ∀ i, w i ∈ subseqLimits G d := fun i => hy'Ω (g i)
  obtain ⟨ψ, hψΩ, hψagree⟩ := exists_mem_subseqLimits_agree w hwΩ
  have hψdp : DoublyPeriodic ψ := hlim ψ hψΩ
  -- `ψ` inherits the bad inequality at `zstar` from a single window comparison.
  have hψbad : ψ (zstar + ϖ) ≠ ψ zstar := by
    obtain ⟨i, -, hi⟩ := hψagree {zstar, zstar + ϖ} 0
    have h1 : ψ zstar = w i zstar := hi zstar (by simp)
    have h2 : ψ (zstar + ϖ) = w i (zstar + ϖ) := hi (zstar + ϖ) (by simp)
    rw [h1, h2]
    exact hstarbad (g i) (hg_mem i)
  -- Take a period `λ` of `ψ` with `pi v λ = Tr(ψ) > 0`.
  have hv : Primitive v := Primitive_of_det_eq_one hvu
  obtain ⟨lam, hlamper, hlameq⟩ := exists_mem_Per_pi_eq_trace hv hψdp
  have hlampos : 0 < pi v lam := by rw [hlameq]; exact_mod_cast trace_pos hv hψdp
  -- Goodness at the row of `zstar - lam`, re-derived from `hgood2` for a large enough index.
  have hψgood : ψ ((zstar - lam) + ϖ) = ψ (zstar - lam) := by
    have hthresh : ∃ M0 : ℕ, ∀ i, M0 ≤ i →
        (pi v zstar - pi v lam < r (g i)) ∧
        (-(N (e (g i)) : ℤ) + (q (g i)) * δ ≤ pi v zstar - pi v lam) := by
      have hrstar : ∀ j ∈ J, r j = pi v zstar := by
        intro j hj
        have hFeq : F j = b := hj
        have h2 : modFin δ.toNat hδnatpos (r j) = b.2 := congrArg Prod.snd hFeq
        rw [hzstardef, pi_add, pi_smul, pi_smul]
        have hpivv : pi v v = 0 := det_self v
        have hpivu : pi v u = 1 := hvu
        rw [hpivv, hpivu]
        rw [← hrval j, h2]
        ring
      refine ⟨(pi v ϖ + pi v lam).toNat + 1, fun i hi => ?_⟩
      have hrgi : r (g i) = pi v zstar := hrstar (g i) (hg_mem i)
      have hxgt_gi := hxgt (g i)
      have hNgi : (i : ℤ) ≤ (N (e (g i)) : ℤ) := by
        have h1 : i ≤ g i := hg_mono i
        have h2 : g i ≤ e (g i) := he_mono (g i)
        have h3 : e (g i) ≤ N (e (g i)) := hNmono (e (g i))
        exact_mod_cast (h1.trans h2).trans h3
      constructor
      · rw [hrgi]; omega
      · have hqr_gi : x (g i) + (q (g i)) * δ = r (g i) := by
          have h1 := Int.mul_ediv_add_emod (x (g i)) δ
          show x (g i) + (-(x (g i) / δ)) * δ = x (g i) % δ
          linear_combination -h1
        have hqd : (q (g i)) * δ = r (g i) - x (g i) := by omega
        rw [hqd, hrgi]
        omega
    -- Use `hthresh` to extract a window instance witnessing goodness at the row of `zstar - lam`.
    obtain ⟨M0, hM0⟩ := hthresh
    obtain ⟨i, hiM0, hiagree⟩ :=
      hψagree ({zstar - lam, zstar - lam + ϖ} : Finset (ℤ × ℤ)) M0
    have h1 : ψ (zstar - lam) = w i (zstar - lam) := hiagree _ (by simp)
    have h2 : ψ (zstar - lam + ϖ) = w i (zstar - lam + ϖ) := hiagree _ (by simp)
    have hzeq2 : pi v (zstar - lam) = pi v zstar - pi v lam := by rw [pi_sub]
    have hgi := hM0 i hiM0
    have hgoodinst : y' (g i) ((zstar - lam) + ϖ) = y' (g i) (zstar - lam) :=
      hgood2 (g i) (pi v zstar - pi v lam) hgi.2 hgi.1 (zstar - lam) hzeq2
    rw [h2, h1]
    exact hgoodinst
  -- Combine `hψgood` with `lam ∈ Per ψ` to contradict `hψbad`.
  have hcombine : ψ (zstar + ϖ) = ψ zstar := by
    have hraw1 := Per.apply hlamper (zstar - lam + ϖ)
    have heq1 : (zstar - lam + ϖ) + lam = zstar + ϖ := by abel
    rw [heq1] at hraw1
    have hraw2 := Per.apply hlamper (zstar - lam)
    have heq2 : (zstar - lam) + lam = zstar := by abel
    rw [heq2] at hraw2
    rw [hraw1, hψgood, ← hraw2]
  exact hψbad hcombine

end Nivat
