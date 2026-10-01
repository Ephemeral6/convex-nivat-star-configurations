/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: lane-hroom-close
-/
import Nivat.External.Colle.TwoMGon

/-!
# `PolyFan` coverage: locating the bracket index

`TwoMGon.lean`'s `face_subset_singleton_of_bracket` collapses `face (PolyShape F) n` to a
single vertex **once the bracket index `i` is known** (`0 < det (F.N i) (F.N (i+1))`,
`0 < det n (F.N (i+1))`, `0 < det (F.N i) n`). What it does not supply is a way to *find* `i`
for an arbitrary primitive `n ∉ Set.range F.N`.

`b3_colle2.txt:298` defines `𝒮_φ := conv(-supp(φ)) ∩ ℤ²` — a genuine bounded convex lattice
polygon, not an abstract fan. `:424`, `:541`, and `:764` each restate the same convention: the
indexing `N 0, …, N (2m-1)` is not an arbitrary enumeration of `E(𝒮_φ)`, it is "an enumeration
… where the edge parallel to `ℓ_{i+1}` is a **successor** of the edge parallel to `ℓ_i`" — i.e.
the boundary-traversal (counterclockwise) order of `𝒮_φ`. For such an order, convexity of
`𝒮_φ` forces two facts that plain `hEeq`/`hadj` do not: (1) consecutive normals turn the same
way (`0 < det (N i) (N (i+1))` for every `i`), and (2) the `2m` open cones between consecutive
normals, together with the `2m` rays `ℝ_{>0} • N i`, tile the plane exactly once — so every
`n ∉ Set.range N` lands in exactly one bracket. Neither fact is derivable from `hEeq`/`hadj`
alone (see `TwoMGon.lean`'s "Toward the general bracket-existence lemma" section for a
discussion of why `hadj`'s purely *local* non-betweenness content stops short of this *global*
statement) — they are part of what "the `N i` enumerate `𝒮_φ`'s edges in boundary order" means,
so we take them as fields, exactly as `hEeq` itself is a field of `PolyFan` and not something
proved from `hlc` alone (`lane-cd-fanscope-instance.lean` §(c) makes this same point about
`hEeq` concretely, on the `m = 2` unit square).

This file adds those two fields (`hccwStep`, `hcover`), checks them against the concrete
`hexFan3` instance (via the same six-way sign case-split `ShellSweep.face_subsingleton_hexShape`
already uses — the check is not vacuous: the six cases are exhaustive and pairwise distinct),
and states the consumer-facing existence theorem.
-/

set_option autoImplicit false

namespace Nivat.TwoMGon

open Nivat Nivat.LE2 Nivat.ShellSweep

/-- A `PolyFan` whose indexing is the actual boundary-traversal order of its polygon: normals
turn the same way at every step (`hccwStep`), and every primitive direction not already a
normal falls strictly between two consecutive ones (`hcover`). `b3_colle2.txt:298,424,541,764`. -/
structure PolyFanCov (m : ℕ) [NeZero m] extends PolyFan m where
  hccwStep : ∀ i : Fin (2 * m), 0 < det (N i) (N (i + 1))
  hcover : ∀ n : ℤ × ℤ, Prim n → n ∉ Set.range N →
    ∃ i : Fin (2 * m), 0 < det (N i) n ∧ 0 < det n (N (i + 1))

/-- **The consumer-facing existence theorem.** For a `PolyFanCov`, every primitive direction
outside the normal set collapses the face to a single vertex — no per-instance case analysis
needed beyond what `hcover` supplies. -/
theorem exists_face_singleton_of_ne_range {m : ℕ} [NeZero m] (F : PolyFanCov m) {n : ℤ × ℤ}
    (hp : Prim n) (hn : n ∉ Set.range F.N) :
    ∃ v, face (PolyShape F.toPolyFan) n ⊆ {v} := by
  obtain ⟨i, hβ, hα⟩ := F.hcover n hp hn
  exact ⟨F.v i, face_subset_singleton_of_bracket F.toPolyFan i (F.hccwStep i) hα hβ⟩

/-! ## `hexFan3` satisfies `hccwStep`/`hcover` -/

private theorem hex3_hccwStep : ∀ i : Fin 6, 0 < det (hex3N i) (hex3N (i + 1)) := by decide

/-- The same six-way sign case-split `ShellSweep.face_subsingleton_hexShape` runs, but stopping
at "which bracket" instead of continuing on to the vertex — confirms `hcover` is not vacuous
(all six cases occur and are pairwise exclusive by `omega`, exactly as in the source lemma). -/
private theorem hex3_cover : ∀ n : ℤ × ℤ, Prim n → n ∉ Set.range hex3N →
    ∃ i : Fin 6, 0 < det (hex3N i) n ∧ 0 < det n (hex3N (i + 1)) := by
  intro n hp hn
  rw [hex3_range_eq] at hn
  have hne : n.1 ≠ 0 ∧ n.2 ≠ 0 ∧ n.1 + n.2 ≠ 0 := by
    refine ⟨fun h0 => hn ?_, fun h0 => hn ?_, fun h0 => hn ?_⟩
    · rcases prim_eq_of_fst_eq_zero hp h0 with rfl | rfl <;> simp [hexE]
    · rcases prim_eq_of_snd_eq_zero hp h0 with rfl | rfl <;> simp [hexE]
    · rcases prim_eq_of_coord_eq_neg hp (by omega) with rfl | rfl <;> simp [hexE]
  obtain ⟨hp0, hq0, hpq0⟩ := hne
  rcases lt_or_gt_of_ne hp0 with hp' | hp' <;> rcases lt_or_gt_of_ne hq0 with hq' | hq' <;>
    rcases lt_or_gt_of_ne hpq0 with hpq' | hpq'
  · exact ⟨3, by simp [hex3N, det]; omega, by simp [hex3N, det]; omega⟩
  · omega
  · exact ⟨2, by simp [hex3N, det]; omega, by simp [hex3N, det]; omega⟩
  · exact ⟨1, by simp [hex3N, det]; omega, by simp [hex3N, det]; omega⟩
  · exact ⟨4, by simp [hex3N, det]; omega, by simp [hex3N, det]; omega⟩
  · exact ⟨5, by simp [hex3N, det]; omega, by simp [hex3N, det]; omega⟩
  · omega
  · exact ⟨0, by simp [hex3N, det]; omega, by simp [hex3N, det]; omega⟩

def hexFan3Cov : PolyFanCov 3 where
  toPolyFan := hexFan3
  hccwStep := hex3_hccwStep
  hcover := hex3_cover

end Nivat.TwoMGon

#print axioms Nivat.TwoMGon.exists_face_singleton_of_ne_range
#print axioms Nivat.TwoMGon.hexFan3Cov
