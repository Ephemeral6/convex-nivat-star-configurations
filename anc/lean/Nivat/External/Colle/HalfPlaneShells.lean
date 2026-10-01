/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Lemma35
import Nivat.External.Colle.LatticeEdges

/-!
# Shell family construction for half-plane coverage

Auxiliary lemmas for Lemma 4.5: constructing shell families that cover half-planes
via generating set propagation.

## Main results

* `exists_vertex_of_generating` — extract a generating vertex from a generating set
* `shellFamily` — the shell family construction, hoisted to a top-level definition
* `not_exists_U_of_shellCondition_counterexample` — the shell condition plus `U 0 = S`
  cannot cover a half-plane, for explicit data satisfying every hypothesis that the
  withdrawn `exists_shell_family_covering_halfplane` imposed

## Status (as of 2026-09-16)

**This file is sorry-free.**  It reached that state by withdrawal, not by proof.

`exists_shell_family_covering_halfplane` was removed on 2026-09-16.  It was false as
stated — the refutation is in this file and was measured clean on that date — it had no
consumers, and Collé's Lemma 4.5 (`scratch/b3_colle2.txt:768-798`) propagates from an
infinite half-strip rather than from a finite single-vertex shell, so there was nothing to
restate it against.  See the withdrawal note above the counterexample below.

Earlier revisions of this header described its `sorry` as something that "can be treated
as a geometric axiom".  That advice was wrong and is retracted: the statement is refuted
in this very file, so admitting it as an axiom would make the development inconsistent.

What survives is genuine: `exists_vertex_of_generating` is proved, and the shell-family
definitions are available for a future, correctly hypothesised version of Lemma 4.5.
-/

namespace Nivat.Colle

open Nivat.LE2

variable {α : Type*}

/-- Extract a generating vertex from a generating set.

We pick `a` to be the (unique) maximizer over `S` of the integer linear functional
`g z = N * z.1 + z.2`, where `N` is chosen larger than the spread of the second
coordinates of points of `S`. This makes `g` injective on `S`: two distinct points
of `S` are separated because any change in the first coordinate dominates any
possible change in the second. Hence the maximizer is a *strict* maximizer of `g`.
A strict maximizer of a real-linear functional over a finite point set is never a
nontrivial convex combination of the other points, i.e. it is an extreme point of
the hull, so deleting it preserves lattice convexity. -/
theorem exists_vertex_of_generating {A : Type*} {ξ : Config A}
    {S : Finset (ℤ × ℤ)} (hgen : IsGeneratingSet ξ S) :
    ∃ a ∈ S, LatticeConvex (S.erase a) ∧ GeneratesAt ξ S a := by
  obtain ⟨hne, hconv, hvert⟩ := hgen

  classical
  have ⟨a, ha, ha_conv⟩ : ∃ a ∈ S, LatticeConvex (S.erase a) := by
    have hyne : (S.image Prod.snd).Nonempty := hne.image _
    set D : ℤ := (S.image Prod.snd).sup' hyne id - (S.image Prod.snd).inf' hyne id with hD
    set N : ℤ := D + 1 with hN
    obtain ⟨z0, hz0⟩ := id hne
    have hDnn : (0 : ℤ) ≤ D := by
      have h1 := Finset.inf'_le (s := S.image Prod.snd) id (Finset.mem_image_of_mem _ hz0)
      have h2 := Finset.le_sup' (s := S.image Prod.snd) id (Finset.mem_image_of_mem _ hz0)
      rw [hD]; linarith
    set g : ℤ × ℤ → ℤ := fun z => N * z.1 + z.2 with hgdef
    -- `g` is injective on `S`.
    have hginj : ∀ z ∈ S, ∀ w ∈ S, g z = g w → z = w := by
      intro z hz w hw heq
      by_contra hne'
      have heq' : N * (z.1 - w.1) = w.2 - z.2 := by
        have hlin : N * z.1 - N * w.1 = w.2 - z.2 := by
          simp only [hgdef] at heq; linarith
        rw [mul_sub]; exact hlin
      have hz2ge : (S.image Prod.snd).inf' hyne id ≤ z.2 :=
        Finset.inf'_le id (Finset.mem_image_of_mem _ hz)
      have hz2le : z.2 ≤ (S.image Prod.snd).sup' hyne id :=
        Finset.le_sup' id (Finset.mem_image_of_mem _ hz)
      have hw2ge : (S.image Prod.snd).inf' hyne id ≤ w.2 :=
        Finset.inf'_le id (Finset.mem_image_of_mem _ hw)
      have hw2le : w.2 ≤ (S.image Prod.snd).sup' hyne id :=
        Finset.le_sup' id (Finset.mem_image_of_mem _ hw)
      have hbound : |w.2 - z.2| ≤ D := by
        rw [abs_le]; rw [hD]; constructor <;> linarith
      rw [← heq'] at hbound
      by_cases hxeq : z.1 = w.1
      · have hy0 : w.2 - z.2 = 0 := by rw [← heq', hxeq]; ring
        exact hne' (Prod.ext hxeq (by linarith))
      · have hd1 : (1 : ℤ) ≤ |z.1 - w.1| :=
          Int.one_le_abs (sub_ne_zero.mpr hxeq)
        have hNpos : (0 : ℤ) < N := by omega
        have hNle : N ≤ |N * (z.1 - w.1)| := by
          rw [abs_mul, abs_of_pos hNpos]
          calc N = N * 1 := (mul_one N).symm
          _ ≤ N * |z.1 - w.1| := mul_le_mul_of_nonneg_left hd1 (le_of_lt hNpos)
        omega
    -- The `g`-maximizer over `S`.
    obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image S g hne
    refine ⟨a, ha, ?_⟩
    -- `a` is a *strict* maximizer of `g` on `S.erase a`.
    have hstrict : ∀ b ∈ S.erase a, (g b : ℝ) < (g a : ℝ) := by
      intro b hb
      obtain ⟨hba, hbS⟩ := Finset.mem_erase.mp hb
      have h1 : g b ≤ g a := hmax b hbS
      have h2 : g b ≠ g a := fun h => hba (hginj b hbS a ha h)
      exact_mod_cast lt_of_le_of_ne h1 h2
    -- The real-linear functional realizing `g`, bundled so `map_sum`/`map_smul` apply.
    set G : (ℝ × ℝ) →ₗ[ℝ] ℝ := (N : ℝ) • LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ with hGdef
    have hGtoReal : ∀ z : ℤ × ℤ, G (toReal z) = (g z : ℝ) := by
      intro z
      simp only [hGdef, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.fst_apply,
        LinearMap.snd_apply, smul_eq_mul, toReal, hgdef]
      push_cast; ring
    -- `a` is not in the real convex hull of `S.erase a`.
    have haux : toReal a ∉ Conv (S.erase a) := by
      intro hmem
      have himg : Conv (S.erase a) =
          convexHull ℝ (((S.erase a).image toReal : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
        rw [Conv, Finset.coe_image]
      rw [himg] at hmem
      obtain ⟨w, hw0, hw1, hwsum⟩ := Finset.mem_convexHull'.mp hmem
      have hw1' : ∑ b ∈ S.erase a, w (toReal b) = 1 := by
        rwa [Finset.sum_image (fun x _ y _ h => toReal_injective h)] at hw1
      have hwsum' : ∑ b ∈ S.erase a, w (toReal b) • toReal b = toReal a := by
        rwa [Finset.sum_image (fun x _ y _ h => toReal_injective h)] at hwsum
      have hGsum : ∑ b ∈ S.erase a, w (toReal b) * G (toReal b) = G (toReal a) := by
        rw [← hwsum', map_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [map_smul, smul_eq_mul]
      have hle : ∀ b ∈ S.erase a, w (toReal b) * G (toReal b) ≤ w (toReal b) * G (toReal a) := by
        intro b hb
        have hGb : G (toReal b) ≤ G (toReal a) := by
          rw [hGtoReal, hGtoReal]; exact le_of_lt (hstrict b hb)
        exact mul_le_mul_of_nonneg_left hGb (hw0 (toReal b) (Finset.mem_image_of_mem _ hb))
      have hex : ∃ b ∈ S.erase a, 0 < w (toReal b) := by
        by_contra hcon
        push_neg at hcon
        have hall0 : ∀ b ∈ S.erase a, w (toReal b) = 0 := fun b hb =>
          le_antisymm (hcon b hb) (hw0 (toReal b) (Finset.mem_image_of_mem _ hb))
        rw [Finset.sum_congr rfl hall0] at hw1'
        simp at hw1'
      have hlt : ∃ b ∈ S.erase a, w (toReal b) * G (toReal b) < w (toReal b) * G (toReal a) := by
        obtain ⟨b0, hb0, hb0pos⟩ := hex
        refine ⟨b0, hb0, ?_⟩
        have hGb0 : G (toReal b0) < G (toReal a) := by
          rw [hGtoReal, hGtoReal]; exact hstrict b0 hb0
        exact mul_lt_mul_of_pos_left hGb0 hb0pos
      have hcontra : G (toReal a) < G (toReal a) := by
        calc G (toReal a) = ∑ b ∈ S.erase a, w (toReal b) * G (toReal b) := hGsum.symm
        _ < ∑ b ∈ S.erase a, w (toReal b) * G (toReal a) := Finset.sum_lt_sum hle hlt
        _ = (∑ b ∈ S.erase a, w (toReal b)) * G (toReal a) := by rw [Finset.sum_mul]
        _ = G (toReal a) := by rw [hw1']; ring
      exact lt_irrefl _ hcontra
    -- Conclude `LatticeConvex (S.erase a)`.
    intro z hz
    have hzS : z ∈ S :=
      hconv z (convexHull_mono (Set.image_mono (S.erase_subset a)) hz)
    have hzne : z ≠ a := by
      intro h; subst h; exact haux hz
    exact Finset.mem_erase.mpr ⟨hzne, hzS⟩

  have ha_gen : GeneratesAt ξ S a := hvert a ha ha_conv

  exact ⟨a, ha, ha_conv, ha_gen⟩

/-- The shell family construction, hoisted to a top-level definition so that
`rfl`/`cases`/`induction` can see through it definitionally.

`shellFamily ξ S a ℓ n` is the `n`-th shell in the propagation of the generating
set `S` from vertex `a`, restricted to the half-plane `halfPlaneLE ℓ 0`. -/
def shellFamily {A : Type*} (_ξ : Config A) (S : Finset (ℤ × ℤ)) (a ℓ : ℤ × ℤ) :
    ℕ → Set (ℤ × ℤ)
  | 0 => S
  | n + 1 => shellFamily _ξ S a ℓ n ∪
      {z | ∃ t : ℤ × ℤ, z = a + t ∧ z ∈ halfPlaneLE ℓ 0 ∧
             ∀ b ∈ S.erase a, b + t ∈ shellFamily _ξ S a ℓ n}

@[simp] theorem shellFamily_zero {A : Type*} (ξ : Config A) (S : Finset (ℤ × ℤ))
    (a ℓ : ℤ × ℤ) : shellFamily ξ S a ℓ 0 = S := rfl

@[simp] theorem shellFamily_succ {A : Type*} (ξ : Config A) (S : Finset (ℤ × ℤ))
    (a ℓ : ℤ × ℤ) (n : ℕ) :
    shellFamily ξ S a ℓ (n + 1) = shellFamily ξ S a ℓ n ∪
      {z | ∃ t : ℤ × ℤ, z = a + t ∧ z ∈ halfPlaneLE ℓ 0 ∧
             ∀ b ∈ S.erase a, b + t ∈ shellFamily ξ S a ℓ n} := rfl

/-! ### Lemma 4.5 shell propagation — statement withdrawn 2026-09-16

A theorem `exists_shell_family_covering_halfplane` stood here, carrying a `sorry` for the
coverage direction.  It was **withdrawn, not proved and not weakened**:

* It is **false as it was stated**.  `not_exists_U_of_shellCondition_counterexample` below
  refutes its conclusion at `S = {(0,0),(1,0)}`, `a = (0,0)`, `ℓ = (0,1)`, and every one of
  its four hypotheses holds for that data (see the counterexample's docstring).  Measured
  2026-09-16, that refutation depends only on `[propext, Classical.choice, Quot.sound]`.
* It had **no consumers** anywhere in the project.
* There is **no source statement to restate it against**.  Collé's Lemma 4.5
  (`scratch/b3_colle2.txt:768-798`) propagates from an infinite half-strip `H_B(ℓ)`
  (`:778`) and uses `A_1 := R_{ι-1} ∩ l_1` (`:794-796`); it does not propagate outward
  from a finite single-vertex shell.  `shellFamily` is this repository's own abstraction,
  and the missing structural hypothesis is the two-sided edge structure discussed under
  `IsRegion₂`, which `LatticeConvex` alone does not capture.

`shellFamily`, `shellFamily_succ` and the proved vertex lemma `exists_vertex_of_generating`
are kept; so is the refutation, as the record of why. -/

/-- **Counterexample showing the coverage direction cannot be strengthened as stated.**

Take `S = {(0,0),(1,0)}`, `a = (0,0)`, `ℓ = (0,1)`, and let `ξ` be any constant
configuration (so `orbitClosure ξ = {ξ}` and `GeneratesAt` holds vacuously for it).
Every hypothesis of `exists_shell_family_covering_halfplane` is satisfied for this
data: `GeneratesAt ξ S a` holds, `S` is lattice-convex (it is the two lattice points
of a primitive segment), `S ⊆ halfPlaneLE (0,1) 0 = {z | z.2 ≤ 0}`, and `(0,1)` is
primitive. Yet **no** `U : ℕ → Set (ℤ × ℤ)` can satisfy both the initial condition
`U 0 = S` and the shell condition and also cover the whole half-plane: by induction
on `n`, every `U n` is forced to lie entirely in the row `{z | z.2 = 0}`, because a
new point `a + t` is only ever admitted once `(1, 0) + t ∈ U n`, and by the inductive
hypothesis this pins `t.2 = 0`. So `⋃ n, U n ⊆ {z | z.2 = 0}`, which never contains,
e.g., `(0, -1) ∈ halfPlaneLE (0,1) 0`.

This shows the withdrawn `exists_shell_family_covering_halfplane`, exactly as it was
stated (with no hypothesis beyond `GeneratesAt`/`LatticeConvex`/`hS_in`/`Primitive`), was
**not a provable theorem**: its `sorry` could not have been discharged without adding a
genuinely stronger structural hypothesis on `S` and `a` — matching Collé's actual
two-sided generating shape (cf. the project's `IsRegion₂`/edge-structure discussion),
which is not captured by `LatticeConvex` alone. This is independent of the vertex
lemma `exists_vertex_of_generating` proved above (no axiom of that lemma is used
here). -/
theorem not_exists_U_of_shellCondition_counterexample :
    ¬ ∃ U : ℕ → Set (ℤ × ℤ),
      (U 0 = (({(0, 0), (1, 0)} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ))) ∧
      (∀ n, ∀ z ∈ U (n + 1),
        z ∈ U n ∨ ∃ t : ℤ × ℤ, z = (0, 0) + t ∧
          ∀ b ∈ (({(0, 0), (1, 0)} : Finset (ℤ × ℤ))).erase (0, 0), b + t ∈ U n) ∧
      (⋃ n, U n = halfPlaneLE (0, 1) 0) := by
  rintro ⟨U, hU0, hshell, hcov⟩
  have hb1 : (1, 0) ∈ (({(0, 0), (1, 0)} : Finset (ℤ × ℤ))).erase (0, 0) := by decide
  have hrow : ∀ n, U n ⊆ {z : ℤ × ℤ | z.2 = 0} := by
    intro n
    induction n with
    | zero =>
      rw [hU0]
      intro z hz
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl <;> rfl
    | succ n ih =>
      intro z hz
      rcases hshell n z hz with h1 | ⟨t, rfl, ht⟩
      · exact ih h1
      · have hmem := ih (ht (1, 0) hb1)
        simp only [Set.mem_ofPred_eq, Prod.snd_add] at hmem ⊢
        simpa using hmem
  have hmemU : ((0, -1) : ℤ × ℤ) ∈ ⋃ n, U n := by
    rw [hcov]
    show dot (0, 1) (0, -1) ≤ 0
    simp [dot]
  rw [Set.mem_iUnion] at hmemU
  obtain ⟨n, hn⟩ := hmemU
  have hcontra := hrow n hn
  simp only [Set.mem_ofPred_eq] at hcontra
  exact absurd hcontra (by decide)

end Nivat.Colle

#print axioms Nivat.Colle.exists_vertex_of_generating
#print axioms Nivat.Colle.shellFamily_zero
#print axioms Nivat.Colle.shellFamily_succ
#print axioms Nivat.Colle.not_exists_U_of_shellCondition_counterexample
