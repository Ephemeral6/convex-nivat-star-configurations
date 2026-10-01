/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.Defs.Complexity
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Orbit closures and local functions

Formalisation of the orbit closure `X = closure {T^u θ : u ∈ ℤ²}` used in §2.1, §4, §8 of
*The Convex Nivat Conjecture* (Pan), and of the notion of a *local function*
of a configuration, used in Lemma 1.1, Lemma 2.4(a), Lemma 4.2 and Lemma 8.5(a).

The product topology on `ℤ² → α` with `α` discrete is not imported; instead the closure is
characterised directly — `x ∈ X` iff every finite window of `x` is a window of some translate
of `θ`.  This is the definition used everywhere in the paper ("a limit in the product topology
agreeing with some translate on any finite window", §8.6 step (5)).

Compactness of `α^{ℤ²}` is likewise not imported from the topology library: the one place it is
needed, `Nivat.subseqLimits_nonempty`, is proved by pushing an ultrafilter refining `atTop`
forward along `n ↦ G (w + n d)` for each `w` separately, which is exactly the diagonal argument
that compactness of a product of finite discrete spaces encodes.

## Main definitions

* `Nivat.orbitClosure` — `X = closure of the orbit`.
* `Nivat.IsLocal` — `g` is a local function of `θ` with a given finite window.
* `Nivat.subseqLimits` — the pointwise subsequential limits of `n ↦ T^{n d} G`.

## Status

Complete; no `sorry`.
-/

namespace Nivat

variable {α : Type*}

/-- The orbit closure of `θ`: the configurations every one of whose finite windows occurs as
a window of a translate of `θ`.  This is the closure of `{T^u θ}` in the product topology of
the discrete topology on `α`.  Paper §2.1. -/
def orbitClosure (θ : Config α) : Set (Config α) :=
  {x | ∀ W : Finset (ℤ × ℤ), ∃ u : ℤ × ℤ, ∀ w ∈ W, x w = θ (u + w)}

theorem mem_orbitClosure_iff {θ x : Config α} :
    x ∈ orbitClosure θ ↔ ∀ W : Finset (ℤ × ℤ), ∃ u : ℤ × ℤ, ∀ w ∈ W, x w = θ (u + w) := Iff.rfl

theorem T_mem_orbitClosure (θ : Config α) (u : ℤ × ℤ) : T u θ ∈ orbitClosure θ :=
  fun _ => ⟨u, fun w _ => by simp [T, add_comm]⟩

theorem self_mem_orbitClosure (θ : Config α) : θ ∈ orbitClosure θ := by
  simpa using T_mem_orbitClosure θ 0

/-- Every finite-window pattern of a member of the orbit closure is a pattern of `θ`.
Paper §8.6, step (5). -/
theorem patterns_subset_of_mem_orbitClosure {θ x : Config α} (hx : x ∈ orbitClosure θ)
    (W : Finset (ℤ × ℤ)) : patterns x W ⊆ patterns θ W := by
  classical
  rintro _ ⟨u, rfl⟩
  obtain ⟨u₀, hu₀⟩ := hx (W.image fun q => u + q)
  refine ⟨u₀ + u, ?_⟩
  funext q
  have hq : u + (q : ℤ × ℤ) ∈ W.image fun q => u + q :=
    Finset.mem_image.mpr ⟨(q : ℤ × ℤ), q.2, rfl⟩
  show θ (u₀ + u + (q : ℤ × ℤ)) = x (u + (q : ℤ × ℤ))
  rw [hu₀ _ hq, add_assoc]

/-- Hence the complexity does not increase along the orbit closure: `P_x(W) ≤ P_θ(W)`.
Paper (8.1).

The finiteness hypothesis cannot be dropped: `Set.ncard` of an infinite set is `0`.  For a
finite alphabet use `Nivat.patterns_finite`, and for a configuration of finite range — the
situation of §8, where the alphabet sits inside `ℤ` — use
`Nivat.patterns_finite_of_range_finite`. -/
theorem P_le_of_mem_orbitClosure {θ x : Config α} (hx : x ∈ orbitClosure θ)
    (W : Finset (ℤ × ℤ)) (hfin : (patterns θ W).Finite) : P x W ≤ P θ W :=
  Set.ncard_le_ncard (patterns_subset_of_mem_orbitClosure hx W) hfin

/-- The orbit closure is closed under translation. -/
theorem T_mem_of_mem_orbitClosure {θ x : Config α} (hx : x ∈ orbitClosure θ) (u : ℤ × ℤ) :
    T u x ∈ orbitClosure θ := by
  classical
  intro W
  obtain ⟨u₀, hu₀⟩ := hx (W.image fun w => w + u)
  refine ⟨u₀ + u, fun w hw => ?_⟩
  have hq : w + u ∈ W.image fun w => w + u := Finset.mem_image.mpr ⟨w, hw, rfl⟩
  show x (w + u) = θ (u₀ + u + w)
  rw [hu₀ _ hq]
  congr 1
  abel

/-- The orbit closure is closed: a configuration all of whose windows agree with windows of
members of `X` lies in `X`. -/
theorem orbitClosure_closed {θ x : Config α}
    (hx : ∀ W : Finset (ℤ × ℤ), ∃ y ∈ orbitClosure θ, ∀ w ∈ W, x w = y w) :
    x ∈ orbitClosure θ := by
  intro W
  obtain ⟨y, hy, hxy⟩ := hx W
  obtain ⟨u, hu⟩ := hy W
  exact ⟨u, fun w hw => (hxy w hw).trans (hu w hw)⟩

-- NOTE (2026-09-17): a duplicate `mem_Per_of_mem_orbitClosure` was added here and removed the
-- same day.  The lemma already exists as `Nivat.Colle.mem_Per_of_mem_orbitClosure`
-- (`Nivat/External/Colle/OrbitClosureBasics.lean:40`), same statement, same two-point-window
-- proof, with the argument order `(hu : u ∈ Per ξ) (hx : x ∈ orbitClosure ξ)` that all six
-- call sites use.  The copy here took its arguments in the opposite order and, sitting in the
-- outer `Nivat` namespace, shadowed the real one at `Theorem114Step3.lean:237-238`, taking
-- `lake build` red.  If this lemma is wanted at `Nivat.Defs` level, *move* the existing one
-- down rather than restating it.

/-- `g : ℤ² → R` is a **local function** of `θ` with window `W` if `g z` depends only on the
pattern of `θ` on `z + W`.  Paper §1.1, §2.4(a), §4, §8.2. -/
def IsLocal {R : Type*} (θ : Config α) (W : Finset (ℤ × ℤ)) (g : Config R) : Prop :=
  ∃ F : (W → α) → R, ∀ z, g z = F (pattern θ W z)

/-- Every pattern of a member of the orbit closure is *literally* a pattern of `θ`: for each
anchor `z` there is an anchor `z'` with `x|_{z+W} = θ|_{z'+W}`. -/
theorem exists_pattern_eq_of_mem_orbitClosure {θ x : Config α} (hx : x ∈ orbitClosure θ)
    (W : Finset (ℤ × ℤ)) (z : ℤ × ℤ) : ∃ z' : ℤ × ℤ, pattern x W z = pattern θ W z' := by
  classical
  obtain ⟨u₀, hu₀⟩ := hx (W.image fun q => z + q)
  refine ⟨u₀ + z, ?_⟩
  funext q
  have hq : z + (q : ℤ × ℤ) ∈ W.image fun q => z + q :=
    Finset.mem_image.mpr ⟨(q : ℤ × ℤ), q.2, rfl⟩
  show x (z + (q : ℤ × ℤ)) = θ (u₀ + z + (q : ℤ × ℤ))
  rw [hu₀ _ hq, add_assoc]

/-- A local identity that holds for `θ` holds throughout the orbit closure: local functions
are continuous for the product topology.  Paper Lemma 2.4(a), Lemma 8.5(a). -/
theorem IsLocal.eq_zero_of_mem_orbitClosure {R : Type*} [Zero R] {θ : Config α}
    {W : Finset (ℤ × ℤ)} {F : (W → α) → R} (hF : ∀ z, F (pattern θ W z) = 0)
    {x : Config α} (hx : x ∈ orbitClosure θ) (z : ℤ × ℤ) : F (pattern x W z) = 0 := by
  obtain ⟨z', hz'⟩ := exists_pattern_eq_of_mem_orbitClosure hx W z
  rw [hz']
  exact hF z'

/-- The set of pointwise subsequential limits of the sequence `n ↦ T^{n • d} G`.  Paper
Proposition 8.14 and Lemma 8.16. -/
def subseqLimits (G : Config α) (d : ℤ × ℤ) : Set (Config α) :=
  {y | ∀ (W : Finset (ℤ × ℤ)) (M : ℕ), ∃ n : ℕ, M ≤ n ∧ ∀ w ∈ W, y w = G (w + (n : ℤ) • d)}

/-- **Compactness of `α^{ℤ²}` for finite `α`**: the sequence `n ↦ T^{n • d} G` always has a
subsequential limit.  Paper Proposition 8.14 ("such a sequence exists by compactness of
`𝔽_p^{ℤ²}`") and Lemma 8.16 ("by compactness, `Ω ≠ ∅`").

The limit is read off from any ultrafilter `𝔲` on `ℕ` refining `atTop`: for each `w` the
pushforward of `𝔲` along `n ↦ G (w + n d)` is an ultrafilter on the finite type `α`, hence
principal at a unique value, and that value is `y w`. -/
theorem subseqLimits_nonempty [Finite α] (G : Config α) (d : ℤ × ℤ) :
    (subseqLimits G d).Nonempty := by
  classical
  set 𝔲 : Ultrafilter ℕ := Ultrafilter.of Filter.atTop with h𝔲
  have key : ∀ w : ℤ × ℤ, ∃ a : α, {n : ℕ | G (w + (n : ℤ) • d) = a} ∈ 𝔲 := by
    intro w
    obtain ⟨a, ha⟩ :=
      Ultrafilter.eq_pure_of_finite (Ultrafilter.map (fun n : ℕ => G (w + (n : ℤ) • d)) 𝔲)
    refine ⟨a, ?_⟩
    have hmem : ({a} : Set α) ∈ Ultrafilter.map (fun n : ℕ => G (w + (n : ℤ) • d)) 𝔲 := by
      rw [ha]; exact Ultrafilter.mem_pure.mpr rfl
    rwa [Ultrafilter.mem_map] at hmem
  choose y hy using key
  refine ⟨y, fun W M => ?_⟩
  have h1 : {n : ℕ | M ≤ n} ∈ 𝔲 := Ultrafilter.of_le Filter.atTop (Filter.mem_atTop M)
  have h2 : (⋂ w ∈ W, {n : ℕ | G (w + (n : ℤ) • d) = y w}) ∈ 𝔲 :=
    (Filter.biInter_finset_mem W).mpr fun w _ => hy w
  obtain ⟨n, hn⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem h1 h2)
  refine ⟨n, hn.1, fun w hw => ?_⟩
  have hn2 := hn.2
  simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hn2
  exact (hn2 w hw).symm

/-- Subsequential limits inherit every period of `G`.  Paper Lemma 8.16 ("pointwise limits
keep the period"). -/
theorem mem_Per_of_mem_subseqLimits {G : Config α} {d : ℤ × ℤ} {y : Config α}
    (hy : y ∈ subseqLimits G d) {u : ℤ × ℤ} (hu : u ∈ Per G) : u ∈ Per y := by
  classical
  rw [mem_Per_iff]
  funext z
  obtain ⟨n, -, hn⟩ := hy {z, z + u} 0
  have h₁ : y (z + u) = G (z + u + (n : ℤ) • d) := hn _ (by simp)
  have h₂ : y z = G (z + (n : ℤ) • d) := hn _ (by simp)
  show y (z + u) = y z
  rw [h₁, h₂, show z + u + (n : ℤ) • d = z + (n : ℤ) • d + u by abel]
  exact Per.apply hu _

/-- Subsequential limits lie in the orbit closure. -/
theorem subseqLimits_subset_orbitClosure (G : Config α) (d : ℤ × ℤ) :
    subseqLimits G d ⊆ orbitClosure G := by
  intro y hy W
  obtain ⟨n, -, hn⟩ := hy W 0
  refine ⟨(n : ℤ) • d, fun w hw => ?_⟩
  rw [hn w hw, add_comm]

/-- The limit set is invariant under `T^d`.  Paper Lemma 8.16. -/
theorem T_mem_subseqLimits {G : Config α} {d : ℤ × ℤ} {y : Config α}
    (hy : y ∈ subseqLimits G d) : T d y ∈ subseqLimits G d := by
  classical
  intro W M
  obtain ⟨n, hnM, hn⟩ := hy (W.image fun w => w + d) M
  refine ⟨n + 1, by omega, fun w hw => ?_⟩
  have hq : w + d ∈ W.image fun w => w + d := Finset.mem_image.mpr ⟨w, hw, rfl⟩
  show y (w + d) = G (w + ((n + 1 : ℕ) : ℤ) • d)
  rw [hn _ hq]
  congr 1
  push_cast
  rw [add_smul, one_smul]
  abel

/-- The limit set is invariant under `T^{-d}`.  Paper Lemma 8.16. -/
theorem T_neg_mem_subseqLimits {G : Config α} {d : ℤ × ℤ} {y : Config α}
    (hy : y ∈ subseqLimits G d) : T (-d) y ∈ subseqLimits G d := by
  classical
  intro W M
  obtain ⟨n, hnM, hn⟩ := hy (W.image fun w => w + -d) (M + 1)
  have hn1 : 1 ≤ n := le_trans (by omega) hnM
  refine ⟨n - 1, by omega, fun w hw => ?_⟩
  have hq : w + -d ∈ W.image fun w => w + -d := Finset.mem_image.mpr ⟨w, hw, rfl⟩
  have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
    have : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn1
    omega
  show y (w + -d) = G (w + ((n - 1 : ℕ) : ℤ) • d)
  rw [hn _ hq, hcast, sub_smul, one_smul]
  congr 1
  abel

/-- The limit set is invariant under `T^d` and `T^{-d}`.  Paper Lemma 8.16. -/
theorem T_subseqLimits (G : Config α) (d : ℤ × ℤ) :
    T d '' subseqLimits G d = subseqLimits G d := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact T_mem_subseqLimits hy
  · intro y hy
    refine ⟨T (-d) y, T_neg_mem_subseqLimits hy, ?_⟩
    rw [← T_add]
    simp

end Nivat
