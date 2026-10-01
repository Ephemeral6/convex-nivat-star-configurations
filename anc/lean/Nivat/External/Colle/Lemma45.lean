/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Lemma35
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.KariMoutot

/-!
# Colle, Lemma 4.5 and Claims 4.6 & 4.11

Formalisation of the final step connecting the sweep induction (Claim 4.3)
to the `colle_region` construction via half-plane intersection and
Szabados-compatible one-sided nonexpansive directions.

From Colle, *On periodic decompositions, one-sided nonexpansive directions and
Nivat's conjecture*, arXiv:1909.08195v4, §4.

## Main results

* `claim46` — under low convex complexity and non-full-periodicity, there exists ℓ ∈ NEL(η)
  with −ℓ, ℓ ∈ ONED(η).  **Unproved (`sorry`)** (E3 updated 2026-09-14).
* `claim411` — Szabados conjecture holds in each ℓ-direction when
  all non-periodic configs have the same order.  **Unproved (`sorry`)** (E3 updated 2026-09-14).

## Refutations (§5)

Two of the three **old** statements were false as written, and §5 proves it.  E3 (2026-09-14)
repaired the signatures; the refutations remain as the record of why the change was needed:

* `low_complexity_implies_directional_agreement_false` and `claim46_false` — a constant
  configuration satisfies the old hypotheses and has a one-point orbit closure.  The missing
  hypothesis was `¬IsFullyPeriodic η` (now added in E3).
* `claim411_false` — the old `SzabadosHoldsInDirection` hard-coded decomposition order `2` where
  the hypothesis only gave order `m`; an explicit order-3 configuration over `(ZMod 2)³` breaks
  it.  E3 generalized `SzabadosHoldsInDirection` to take `m` as a parameter.

Each refutation is stated as the negation of the universally-quantified form of the
corresponding **old** theorem, so that it collided with it head-on: the current statements
with E3's fixes are believed true (though still unproved).

## Dependencies

This file will import once F1/F2 complete:
- `Nivat.External.Colle.Claim43` (F1) — sweep induction `hsweep`
- `Nivat.External.Colle.RegionEdges` (F2) — half-plane intersection

## Status

**2026-09-16 status:** `lemma45` withdrawn (name/content mismatch: it stated Theorem 1.15(ii)'s
conclusion, not Lemma 4.5, and had zero term-level consumers — the six importers of this file
only use `NonExpansiveLine`/`IsOneSidedNonexpansive`; the main line proves the same content via
`exists_biONED_direction`). See `blueprint/NOTE.md` ("`lemma45` 名实不符 + 0 消费者", 2026-09-16)
for the full analysis. The file previously also contained
`low_complexity_implies_directional_agreement`, `claim46`, and `claim411`, all removed
after E3 signature fixes made their refutations inapplicable. See §5 and `blueprint/NOTE.md`.
-/

namespace Nivat.Colle45

open Nivat Nivat.Colle Nivat.Colle35 Nivat.LE2 Nivat.KM

variable {A : Type*} [Fintype A] [Nonempty A] [DecidableEq A] [AddCommMonoid A]

/-! ## §1. Placeholder definitions

Temporary stand-ins to allow compilation before F1/F2 complete.
-/

/-- Placeholder: A minimal periodic decomposition of order m. -/
def IsMinimalPeriodicDecomp {A : Type*} [AddCommMonoid A] (m : ℕ)
    (η : Config A) (ηs : Fin m → Config A) : Prop :=
  (∀ z, η z = ∑ i, ηs i z) ∧ (∀ i, IsPeriodic (ηs i))

/-- Placeholder: Configuration is fully periodic. -/
def IsFullyPeriodic {A : Type*} (η : Config A) : Prop :=
  DoublyPeriodic η

/-- Placeholder: A line direction in NEL(η).

**2026-09-13 fix.**  The guard used to be `∃ t : ℤ, z ∈ halfPlaneLE v t`, which
holds for every `z` (take `t := dot v z`), forcing `x = y` and hence making this
set identically empty.  Same bug as the one that made
`low_complexity_implies_directional_agreement` inconsistent; here it only made
everything downstream vacuous rather than false.  Now uses the fixed half-plane. -/
def NonExpansiveLine {A : Type*} (η : Config A) : Set (ℤ × ℤ) :=
  {v | Primitive v ∧ ∃ x y, x ∈ orbitClosure η ∧ y ∈ orbitClosure η ∧ x ≠ y ∧
    ∀ z ∈ halfPlaneLE v 0, x z = y z}

/-- Placeholder: One-sided nonexpansive in direction ℓ.

**2026-09-13 fix.**  The guard used to be `∀ t, ∀ z, dot ℓ z ≤ t → x z = y z`,
the dual of the `NonExpansiveLine` bug: quantifying `t` universally lets it grow
without bound, so this too forced `x = y` and made the predicate uninhabitable.
Now fixed at `t = 0`, matching `sideOf`/`ONED`. -/
def IsOneSidedNonexpansive {A : Type*} (η : Config A) (ℓ : ℤ × ℤ) : Prop :=
  ∃ x y, x ∈ orbitClosure η ∧ y ∈ orbitClosure η ∧ x ≠ y ∧
    ∀ z, dot ℓ z ≤ 0 → x z = y z

/-- Placeholder: Szabados conjecture holds in direction ℓ with decomposition order m.

**2026-09-14 E3 generalization:** Changed from hardcoded order `2` to parameter `m` to match
the hypothesis structure in `claim411`. -/
def SzabadosHoldsInDirection {A : Type*} [AddCommMonoid A]
    (η : Config A) (m : ℕ) (ℓ : ℤ × ℤ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ R : Set (ℤ × ℤ), ∃ ℓ' : ℤ × ℤ, IsRegion R ℓ ℓ' ∧
    ∀ z, z ∈ R → ∃ (ηs : Fin m → Config A),
      IsMinimalPeriodicDecomp m (T z η) ηs

/-! ## §2. Lemma 4.5

`lemma45` (which stated Colle's Lemma 4.5: if all non-periodic configs have order m ≥ 2, then
for every ℓ ∈ NEL(η), both −ℓ and ℓ are one-sided nonexpansive) was withdrawn 2026-09-16: its
name did not match its content — the conclusion it stated is Theorem 1.15(ii), not Lemma 4.5 —
and it had zero term-level consumers.  The main line proves the corresponding content via
`exists_biONED_direction`.  See `blueprint/NOTE.md` ("`lemma45` 名实不符 + 0 消费者",
2026-09-16) for the full analysis, including the genuine mathematical obstacle it exposed:
passing from agreement on `halfPlaneLE ℓ 0` to agreement on `halfPlaneLE (-ℓ) 0` is not formal,
and the correct statement needs different witness pairs for `ℓ` and `-ℓ`, which routes through
Colle's Proposition 2.10 / Kari–Szabados Proposition 2.12 (itself carrying `sorryAx` in
`Prop210.lean`). -/

/-! ## §3. Refutations of three unproved statements from earlier drafts

Three theorems that appeared in earlier versions of this file
(`low_complexity_implies_directional_agreement`, `claim46`, and `claim411`) have been removed.
They had no downstream callers and required F1/F2 geometric foundations not yet formalized.

The refutation theorems below remain as documentation of what went wrong with the original
signatures:

* **§3.1** — `low_complexity_implies_directional_agreement` was missing the hypothesis
  `¬IsFullyPeriodic η`.  A constant configuration satisfies `LowConvexComplexity` (take
  `S = {0}`: `P η S = 1 = S.card`), has a periodic decomposition of every order, and satisfies
  `hsame` vacuously — every `ξ` in its orbit closure is that same constant, hence doubly
  periodic — yet its orbit closure is a single point, so no pair `x ≠ y` exists at all.
  `claim46` failed on the same configuration for the same reason: `NonExpansiveLine η = ∅`.
  Note that `hlow` is not the culprit: the existential `∃ S` in `LowConvexComplexity` makes
  constant configurations low-complexity by design.

* **§3.2** — `claim411`'s conclusion `SzabadosHoldsInDirection` hard-coded decomposition order
  `2` (`IsMinimalPeriodicDecomp 2 (T z η) ηs`) while its hypothesis `hdecomp` only supplied
  order `m`.  For `m = 3` that is a genuine loss.  The configuration
  `z ↦ (δ z.1, δ z.2, δ (z.1 + z.2))` over `(ZMod 2)³` is a sum of three periodic
  configurations (one per coordinate, with periods `(0,1)`, `(1,0)`, `(1,-1)`), is not a sum of
  two, has trivial period group, and satisfied every hypothesis of `claim411` — including
  `hsame`, because "coordinate `i` has period `h i`" is a two-point local identity and so is
  inherited by the whole orbit closure.  Since `LE2.IsRegion R ℓ ℓ'` forces `R.Infinite`, the
  region produced by the conclusion contains some `z`, and there the conclusion demands an
  order-2 decomposition of `T z η`, which does not exist.  The repair is to replace the `2` in
  `SzabadosHoldsInDirection` by `m`; that edits a definition used outside this file, so it is
  not done here.
-/

section Refutations

/-! ### §5.1 Constant configurations refute `low_complexity_implies_directional_agreement`
and `claim46` -/

/-- The orbit closure of a constant configuration is a single point. -/
theorem eq_of_mem_orbitClosure_const {B : Type*} {a : B} {x : Config B}
    (hx : x ∈ orbitClosure (fun _ : ℤ × ℤ => a)) : x = fun _ => a := by
  funext z
  obtain ⟨u, hu⟩ := hx {z}
  exact hu z (Finset.mem_singleton_self z)

/-- A constant configuration is doubly periodic, i.e. `IsFullyPeriodic`. -/
theorem doublyPeriodic_const {B : Type*} (a : B) :
    DoublyPeriodic (fun _ : ℤ × ℤ => a) := by
  refine ⟨(1, 0), ?_, (0, 1), ?_, ?_⟩
  · rw [mem_Per_iff]; rfl
  · rw [mem_Per_iff]; rfl
  · simp [det]

/-- A constant configuration has low convex complexity: witness `S = {0}`, where
`P θ S = 1 = S.card`. -/
theorem lowConvexComplexity_const {B : Type*} (a : B) :
    LowConvexComplexity (fun _ : ℤ × ℤ => a) := by
  refine ⟨{0}, ⟨0, Finset.mem_singleton_self 0⟩, ?_, ?_⟩
  · intro z hz
    have h : Conv ({0} : Finset (ℤ × ℤ)) = {toReal 0} := by simp [Conv]
    rw [h] at hz
    have := toReal_injective hz
    simpa using this
  · have hp : pattern (fun _ : ℤ × ℤ => a) ({0} : Finset (ℤ × ℤ)) = fun _ => (fun _ => a) := by
      funext u q; rfl
    have h : patterns (fun _ : ℤ × ℤ => a) ({0} : Finset (ℤ × ℤ)) = {fun _ => a} := by
      rw [patterns, hp]
      exact Set.range_const
    simp [P, h]

/-- No line is non-expansive for a constant configuration: there is no pair `x ≠ y` to be had.
-/
theorem nonExpansiveLine_const {B : Type*} (a : B) :
    NonExpansiveLine (fun _ : ℤ × ℤ => a) = ∅ := by
  ext v
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, x, y, hx, hy, hne, -⟩
  exact hne ((eq_of_mem_orbitClosure_const hx).trans (eq_of_mem_orbitClosure_const hy).symm)

/-- The zero configuration has a minimal periodic decomposition of order `2`. -/
theorem const_hdecomp {B : Type*} [AddCommMonoid B] :
    ∃ ηs : Fin 2 → Config B, IsMinimalPeriodicDecomp 2 (fun _ => (0 : B)) ηs :=
  ⟨fun _ _ => 0, by intro z; simp, fun _ => ⟨(1, 0), by rw [mem_Per_iff]; rfl, by simp⟩⟩

/-- The `hsame` hypothesis is vacuous for the zero configuration: every member of its orbit
closure is doubly periodic. -/
theorem const_hsame {B : Type*} [AddCommMonoid B] (m : ℕ) :
    ∀ ξ, ξ ∈ orbitClosure (fun _ => (0 : B)) → ¬IsFullyPeriodic ξ →
      ∃ ξs : Fin m → Config B, IsMinimalPeriodicDecomp m ξ ξs :=
  fun _ hξ hnp =>
    absurd (by rw [eq_of_mem_orbitClosure_const hξ]; exact doublyPeriodic_const 0) hnp

/-- **`low_complexity_implies_directional_agreement` is false as stated.**
Witness: `A = ZMod 2`, `η ≡ 0`, `m = 2`.  All four hypotheses hold; the conclusion asks for
`x ≠ y` in a one-point orbit closure.  The statement needs `¬IsFullyPeriodic η`. -/
theorem low_complexity_implies_directional_agreement_false :
    ¬ ∀ (B : Type) [Fintype B] [Nonempty B] [DecidableEq B] [AddCommMonoid B]
        (η : Config B) (m : ℕ), 2 ≤ m → LowConvexComplexity η →
        (∃ ηs : Fin m → Config B, IsMinimalPeriodicDecomp m η ηs) →
        (∀ ξ, ξ ∈ orbitClosure η → ¬IsFullyPeriodic ξ →
          ∃ ξs : Fin m → Config B, IsMinimalPeriodicDecomp m ξ ξs) →
        ∃ (x y : Config B) (ℓ : ℤ × ℤ),
          x ∈ orbitClosure η ∧ y ∈ orbitClosure η ∧ x ≠ y ∧ Primitive ℓ ∧
          (∀ z, z ∈ halfPlaneLE ℓ 0 → x z = y z) := by
  intro h
  obtain ⟨x, y, ℓ, hx, hy, hne, -, -⟩ :=
    h (ZMod 2) (fun _ => 0) 2 le_rfl (lowConvexComplexity_const 0) const_hdecomp (const_hsame 2)
  exact hne ((eq_of_mem_orbitClosure_const hx).trans (eq_of_mem_orbitClosure_const hy).symm)

/-- **`claim46` is false as stated** — the same constant witness, whose `NonExpansiveLine` is
empty.  (`claim46` is *proved* above, but only from the two `sorry`ed results; this shows that
derivation can never be completed.) -/
theorem claim46_false :
    ¬ ∀ (B : Type) [Fintype B] [Nonempty B] [DecidableEq B] [AddCommMonoid B]
        (η : Config B) (m : ℕ), 2 ≤ m → LowConvexComplexity η →
        (∃ ηs : Fin m → Config B, IsMinimalPeriodicDecomp m η ηs) →
        (∀ ξ, ξ ∈ orbitClosure η → ¬IsFullyPeriodic ξ →
          ∃ ξs : Fin m → Config B, IsMinimalPeriodicDecomp m ξ ξs) →
        ∃ ℓ, ℓ ∈ NonExpansiveLine η ∧
          IsOneSidedNonexpansive η ℓ ∧ IsOneSidedNonexpansive η (-ℓ) := by
  intro h
  obtain ⟨ℓ, hℓ, -, -⟩ :=
    h (ZMod 2) (fun _ => 0) 2 le_rfl (lowConvexComplexity_const 0) const_hdecomp (const_hsame 2)
  rw [nonExpansiveLine_const] at hℓ
  exact hℓ

/-! ### §5.2 A configuration of order three refutes `claim411` -/

namespace Cex411

/-- The alphabet: three independent copies of `ZMod 2`, one per line direction. -/
abbrev A3 : Type := ZMod 2 × ZMod 2 × ZMod 2

/-- The 1-D delta function. -/
def del (k : ℤ) : ZMod 2 := if k = 0 then 1 else 0

/-- Three lines in three different directions, each kept in its own coordinate so that no
cancellation can occur. -/
def eta3 : Config A3 := fun z => (del z.1, del z.2, del (z.1 + z.2))

/-! #### The four-point identity fails in every pair of nonzero directions -/

theorem del_four_point {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ s : ℤ, del s + del (s + a + b) ≠ del (s + a) + del (s + b) := by
  by_cases hab : a + b = 0
  · refine ⟨-a, ?_⟩
    rw [del, del, del, del, if_neg (by omega : (-a : ℤ) ≠ 0),
      if_neg (by omega : (-a + a + b : ℤ) ≠ 0), if_pos (by omega : (-a + a : ℤ) = 0),
      if_neg (by omega : (-a + b : ℤ) ≠ 0)]
    decide
  · refine ⟨0, ?_⟩
    rw [del, del, del, del, if_pos (by omega : (0 : ℤ) = 0),
      if_neg (by omega : (0 + a + b : ℤ) ≠ 0), if_neg (by omega : (0 + a : ℤ) ≠ 0),
      if_neg (by omega : (0 + b : ℤ) ≠ 0)]
    decide

theorem coord_fail (f : ℤ × ℤ → ℤ) (hf : ∀ z w : ℤ × ℤ, f (z + w) = f z + f w)
    (hsurj : Function.Surjective f) {u v : ℤ × ℤ} (hu : f u ≠ 0) (hv : f v ≠ 0) :
    ∃ z : ℤ × ℤ, del (f z) + del (f (z + u + v)) ≠ del (f (z + u)) + del (f (z + v)) := by
  obtain ⟨s, hs⟩ := del_four_point hu hv
  obtain ⟨z, hz⟩ := hsurj s
  refine ⟨z, ?_⟩
  simp only [hf, hz]
  exact hs

/-- For any two nonzero `u`, `v`, at least one of the three coordinates of `eta3` breaks the
identity `ζ z + ζ (z+u+v) = ζ (z+u) + ζ (z+v)`. -/
theorem eta3_four_point {u v : ℤ × ℤ} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ z : ℤ × ℤ, eta3 z + eta3 (z + u + v) ≠ eta3 (z + u) + eta3 (z + v) := by
  have hu' : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
    rcases eq_or_ne u.1 0 with h | h
    · exact Or.inr fun h2 => hu (Prod.ext h h2)
    · exact Or.inl h
  have hv' : v.1 ≠ 0 ∨ v.2 ≠ 0 := by
    rcases eq_or_ne v.1 0 with h | h
    · exact Or.inr fun h2 => hv (Prod.ext h h2)
    · exact Or.inl h
  have htri : (u.1 ≠ 0 ∧ v.1 ≠ 0) ∨ (u.2 ≠ 0 ∧ v.2 ≠ 0) ∨
      (u.1 + u.2 ≠ 0 ∧ v.1 + v.2 ≠ 0) := by omega
  rcases htri with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨z, hz⟩ := coord_fail (fun p => p.1) (fun _ _ => rfl)
      (fun s => ⟨(s, 0), rfl⟩) h1 h2
    exact ⟨z, fun hcon => hz (congrArg (fun p => p.1) hcon)⟩
  · obtain ⟨z, hz⟩ := coord_fail (fun p => p.2) (fun _ _ => rfl)
      (fun s => ⟨(0, s), rfl⟩) h1 h2
    exact ⟨z, fun hcon => hz (congrArg (fun p => p.2.1) hcon)⟩
  · obtain ⟨z, hz⟩ := coord_fail (fun p => p.1 + p.2) (fun z w => by simp; ring)
      (fun s => ⟨(s, 0), by simp⟩) h1 h2
    exact ⟨z, fun hcon => hz (congrArg (fun p => p.2.2) hcon)⟩

/-- A sum of **two** periodic configurations satisfies the four-point identity, with `u`, `v`
the two periods.  No subtraction is used, so this holds in any `AddCommMonoid`. -/
theorem four_point_of_decomp_two {B : Type*} [AddCommMonoid B] {ζ : Config B}
    (h : ∃ ζs : Fin 2 → Config B, IsMinimalPeriodicDecomp 2 ζ ζs) :
    ∃ u v : ℤ × ℤ, u ≠ 0 ∧ v ≠ 0 ∧
      ∀ z, ζ z + ζ (z + u + v) = ζ (z + u) + ζ (z + v) := by
  obtain ⟨ζs, hsum, hper⟩ := h
  obtain ⟨u, hu, hu0⟩ := hper 0
  obtain ⟨v, hv, hv0⟩ := hper 1
  refine ⟨u, v, hu0, hv0, fun z => ?_⟩
  have e : ∀ w, ζ w = ζs 0 w + ζs 1 w := by
    intro w; rw [hsum w, Fin.sum_univ_two]
  have k1 : ζs 0 (z + u + v) = ζs 0 (z + v) := by
    rw [show z + u + v = (z + v) + u from by abel]; exact Per.apply hu _
  have k2 : ζs 1 (z + u + v) = ζs 1 (z + u) := by
    rw [show z + u + v = (z + u) + v from by abel]; exact Per.apply hv _
  rw [e z, e (z + u + v), e (z + u), e (z + v), k1, k2, Per.apply hu z, Per.apply hv z]
  abel

/-! #### Basic facts about `del` and `eta3` -/

theorem del_zero : del 0 = 1 := if_pos rfl

theorem del_eq_zero {k : ℤ} (h : k ≠ 0) : del k = 0 := if_neg h

theorem eta3_eq_zero {z : ℤ × ℤ} (h1 : z.1 ≠ 0) (h2 : z.2 ≠ 0) (h3 : z.1 + z.2 ≠ 0) :
    eta3 z = 0 := by
  show (del z.1, del z.2, del (z.1 + z.2)) = 0
  rw [del_eq_zero h1, del_eq_zero h2, del_eq_zero h3]
  rfl

/-- The all-zero configuration is a limit of translates of `eta3`. -/
theorem zero_mem_orbitClosure : (fun _ => (0 : A3)) ∈ orbitClosure eta3 := by
  classical
  intro W
  refine ⟨(((W.sup fun w => w.1.natAbs + w.2.natAbs : ℕ) : ℤ) + 1,
    ((W.sup fun w => w.1.natAbs + w.2.natAbs : ℕ) : ℤ) + 1), fun w hw => ?_⟩
  have hb : w.1.natAbs + w.2.natAbs ≤ (W.sup fun w => w.1.natAbs + w.2.natAbs) :=
    Finset.le_sup (f := fun w : ℤ × ℤ => w.1.natAbs + w.2.natAbs) hw
  refine (eta3_eq_zero (z := _) ?_ ?_ ?_).symm
  · show ((W.sup fun w => w.1.natAbs + w.2.natAbs : ℕ) : ℤ) + 1 + w.1 ≠ 0
    omega
  · show ((W.sup fun w => w.1.natAbs + w.2.natAbs : ℕ) : ℤ) + 1 + w.2 ≠ 0
    omega
  · show ((W.sup fun w => w.1.natAbs + w.2.natAbs : ℕ) : ℤ) + 1 + w.1 +
      (((W.sup fun w => w.1.natAbs + w.2.natAbs : ℕ) : ℤ) + 1 + w.2) ≠ 0
    omega

/-- A single vertical line at `z.1 = 1`, in the first coordinate only: another limit of
translates of `eta3`, obtained by sending the other two lines to infinity. -/
def yconf : Config A3 := fun z => (del (z.1 - 1), 0, 0)

theorem yconf_mem_orbitClosure : yconf ∈ orbitClosure eta3 := by
  classical
  intro W
  refine ⟨(-1, ((W.sup fun w => w.1.natAbs + w.2.natAbs : ℕ) : ℤ) + 2), fun w hw => ?_⟩
  have hb : w.1.natAbs + w.2.natAbs ≤ (W.sup fun w => w.1.natAbs + w.2.natAbs) :=
    Finset.le_sup (f := fun w : ℤ × ℤ => w.1.natAbs + w.2.natAbs) hw
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show del (w.1 - 1) = del (-1 + w.1)
    exact congrArg del (by omega)
  · show (0 : ZMod 2) =
      del (((W.sup fun w => w.1.natAbs + w.2.natAbs : ℕ) : ℤ) + 2 + w.2)
    exact (del_eq_zero (by omega)).symm
  · show (0 : ZMod 2) = del (-1 + w.1 +
      (((W.sup fun w => w.1.natAbs + w.2.natAbs : ℕ) : ℤ) + 2 + w.2))
    exact (del_eq_zero (by omega)).symm

theorem zero_ne_yconf : (fun _ => (0 : A3)) ≠ yconf := by
  intro h
  have h1 : (0 : ZMod 2) = del ((1 : ℤ) - 1) :=
    congrArg (fun p => p.1) (congrFun h ((1, 0) : ℤ × ℤ))
  rw [show ((1 : ℤ) - 1) = 0 from by omega, del_zero] at h1
  exact zero_ne_one h1

/-- `(1,0)` is a non-expansive line for `eta3`: the zero configuration and `yconf` agree on
`{z | z.1 ≤ 0}` and differ at `(1,0)`. -/
theorem one_zero_mem_NEL : ((1, 0) : ℤ × ℤ) ∈ NonExpansiveLine eta3 := by
  refine ⟨isCoprime_one_left, (fun _ => (0 : A3)), yconf, zero_mem_orbitClosure,
    yconf_mem_orbitClosure, zero_ne_yconf, ?_⟩
  intro z hz
  have hz1 : z.1 ≤ 0 := by
    have : dot (1, 0) z ≤ 0 := hz
    simp only [dot] at this
    omega
  show (0 : A3) = (del (z.1 - 1), 0, 0)
  rw [del_eq_zero (by omega : z.1 - 1 ≠ 0)]
  rfl

/-! #### `eta3` is not doubly periodic, but decomposes into three periodic parts -/

theorem eta3_per_eq_zero {w : ℤ × ℤ} (hw : w ∈ Per eta3) : w = 0 := by
  have h1 : w.1 = 0 := by
    by_contra hc
    have e : del (-w.1 + w.1) = del (-w.1) :=
      congrArg (fun p => p.1) (Per.apply hw ((-w.1, 0) : ℤ × ℤ))
    rw [show (-w.1 + w.1 : ℤ) = 0 from by omega, del_zero,
      del_eq_zero (by omega : (-w.1 : ℤ) ≠ 0)] at e
    exact one_ne_zero e
  have h2 : w.2 = 0 := by
    by_contra hc
    have e : del (-w.2 + w.2) = del (-w.2) :=
      congrArg (fun p => p.2.1) (Per.apply hw ((0, -w.2) : ℤ × ℤ))
    rw [show (-w.2 + w.2 : ℤ) = 0 from by omega, del_zero,
      del_eq_zero (by omega : (-w.2 : ℤ) ≠ 0)] at e
    exact one_ne_zero e
  exact Prod.ext h1 h2

theorem eta3_not_fullyPeriodic : ¬ IsFullyPeriodic eta3 := by
  intro h
  obtain ⟨u, hu, v, hv, hdet⟩ := h
  rw [eta3_per_eq_zero hu, eta3_per_eq_zero hv] at hdet
  exact hdet (by simp [det])

theorem eta3_decomp : ∃ ηs : Fin 3 → Config A3, IsMinimalPeriodicDecomp 3 eta3 ηs := by
  refine ⟨![fun z => (del z.1, 0, 0), fun z => (0, del z.2, 0),
    fun z => (0, 0, del (z.1 + z.2))], ?_, ?_⟩
  · intro z
    rw [Fin.sum_univ_three]
    simp [eta3]
  · intro i
    fin_cases i
    · refine ⟨(0, 1), ?_, by simp⟩
      rw [mem_Per_iff]; funext z
      simp [T]
    · refine ⟨(1, 0), ?_, by simp⟩
      rw [mem_Per_iff]; funext z
      simp [T]
    · refine ⟨(1, -1), ?_, by simp⟩
      rw [mem_Per_iff]; funext z
      simp only [T]
      exact congrArg (fun k => ((0 : ZMod 2), (0 : ZMod 2), del k))
        (show z.1 + 1 + (z.2 + -1) = z.1 + z.2 from by omega)

/-- A one-coordinate local identity of `θ` is inherited by every member of its orbit closure.
-/
theorem coord_period_of_mem_orbitClosure {α β : Type*} (f : α → β) {θ ξ : Config α}
    (hξ : ξ ∈ orbitClosure θ) {d : ℤ × ℤ} (hθ : ∀ w, f (θ (w + d)) = f (θ w)) (z : ℤ × ℤ) :
    f (ξ (z + d)) = f (ξ z) := by
  classical
  obtain ⟨u, hu⟩ := hξ {z, z + d}
  have h1 : ξ z = θ (u + z) := hu z (by simp)
  have h2 : ξ (z + d) = θ (u + (z + d)) := hu _ (by simp)
  rw [h1, h2, show u + (z + d) = (u + z) + d from by abel, hθ]

/-- `hsame` holds for `eta3`, and with no periodicity side condition at all: each coordinate
of each member of the orbit closure inherits the period of the corresponding coordinate of
`eta3`. -/
theorem eta3_hsame (ξ : Config A3) (hξ : ξ ∈ orbitClosure eta3) :
    ∃ ξs : Fin 3 → Config A3, IsMinimalPeriodicDecomp 3 ξ ξs := by
  refine ⟨![fun z => ((ξ z).1, 0, 0), fun z => (0, (ξ z).2.1, 0),
    fun z => (0, 0, (ξ z).2.2)], ?_, ?_⟩
  · intro z
    rw [Fin.sum_univ_three]
    simp
  · intro i
    fin_cases i
    · show IsPeriodic (fun z : ℤ × ℤ => ((ξ z).1, (0 : ZMod 2), (0 : ZMod 2)))
      refine ⟨(0, 1), ?_, by simp⟩
      rw [mem_Per_iff]; funext z
      show (((ξ (z + (0, 1))).1, (0 : ZMod 2), (0 : ZMod 2)) : A3) = ((ξ z).1, 0, 0)
      rw [coord_period_of_mem_orbitClosure (fun p => p.1) hξ (d := (0, 1))
        (fun w => congrArg del (add_zero w.1)) z]
    · show IsPeriodic (fun z : ℤ × ℤ => ((0 : ZMod 2), (ξ z).2.1, (0 : ZMod 2)))
      refine ⟨(1, 0), ?_, by simp⟩
      rw [mem_Per_iff]; funext z
      show (((0 : ZMod 2), (ξ (z + (1, 0))).2.1, (0 : ZMod 2)) : A3) = (0, (ξ z).2.1, 0)
      rw [coord_period_of_mem_orbitClosure (fun p => p.2.1) hξ (d := (1, 0))
        (fun w => congrArg del (add_zero w.2)) z]
    · show IsPeriodic (fun z : ℤ × ℤ => ((0 : ZMod 2), (0 : ZMod 2), (ξ z).2.2))
      refine ⟨(1, -1), ?_, by simp⟩
      rw [mem_Per_iff]; funext z
      show (((0 : ZMod 2), (0 : ZMod 2), (ξ (z + (1, -1))).2.2) : A3) = (0, 0, (ξ z).2.2)
      rw [coord_period_of_mem_orbitClosure (fun p => p.2.2) hξ (d := (1, -1))
        (fun w => congrArg del (show w.1 + 1 + (w.2 + -1) = w.1 + w.2 from by omega)) z]

end Cex411

/-- The old order-2 version of `SzabadosHoldsInDirection`, preserved to make the refutation
`claim411_false` type-check.  This is the statement that was false; the current definition
`SzabadosHoldsInDirection` has been generalized to order `m`. -/
def SzabadosHoldsInDirection_order2 {A : Type*} [AddCommMonoid A]
    (η : Config A) (ℓ : ℤ × ℤ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ R : Set (ℤ × ℤ), ∃ ℓ' : ℤ × ℤ, IsRegion R ℓ ℓ' ∧
    ∀ z, z ∈ R → ∃ (ηs : Fin 2 → Config A),
      IsMinimalPeriodicDecomp 2 (T z η) ηs

open Cex411 in
/-- **`claim411` is false as stated when using the old order-2 `SzabadosHoldsInDirection`.**
Witness: `A = (ZMod 2)³`, `η z = (δ z.1, δ z.2, δ (z.1 + z.2))`, `m = 3`, `ℓ = (1,0)`.
All three hypotheses hold, but the conclusion's old `SzabadosHoldsInDirection_order2` demands an
order-**2** decomposition of `T z η` for every `z` in a region, while `η` genuinely has
order 3.  This refutes the old statement; the current `claim411` uses the generalized
`SzabadosHoldsInDirection η m ℓ` and is believed true (though still unproved). -/
theorem claim411_false :
    ¬ ∀ (B : Type) [Fintype B] [Nonempty B] [DecidableEq B] [AddCommMonoid B]
        (η : Config B) (m : ℕ), ¬IsFullyPeriodic η →
        (∃ ηs : Fin m → Config B, IsMinimalPeriodicDecomp m η ηs) →
        (∀ ξ, ξ ∈ orbitClosure η → ¬IsFullyPeriodic ξ →
          ∃ ξs : Fin m → Config B, IsMinimalPeriodicDecomp m ξ ξs) →
        ∀ ℓ, ℓ ∈ NonExpansiveLine η → SzabadosHoldsInDirection_order2 η ℓ := by
  intro h
  obtain ⟨R, ℓ', hR, hz⟩ :=
    h A3 eta3 3 eta3_not_fullyPeriodic eta3_decomp (fun ξ hξ _ => eta3_hsame ξ hξ)
      (1, 0) one_zero_mem_NEL 1 one_pos
  obtain ⟨z, hzR⟩ := hR.infinite.nonempty
  obtain ⟨u, v, hu, hv, hid⟩ := four_point_of_decomp_two (hz z hzR)
  obtain ⟨w, hw⟩ := eta3_four_point hu hv
  have key := hid (w - z)
  simp only [T] at key
  rw [show w - z + z = w from by abel, show w - z + u + v + z = w + u + v from by abel,
    show w - z + u + z = w + u from by abel, show w - z + v + z = w + v from by abel] at key
  exact hw key

end Refutations

end Nivat.Colle45
