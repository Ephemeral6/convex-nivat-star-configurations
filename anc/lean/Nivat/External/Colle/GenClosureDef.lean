/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Generating

/-!
# `GenClosure`: the unrestricted (multi-generator) generating closure

Moved out of `Claim37.lean:288-308` so that `Lemma35.lean` can depend on it without a cycle
(`Claim37.lean` itself imports `Lemma35.lean`). Content unchanged; this is a pure relocation,
not a new result. `Colle37.GenClosure`/`Colle37.agree_on_genClosure` keep their qualified
names — every existing reference (`Claim37.lean`, `GenClosureWeaken.lean`) still resolves.

Round 80 (`blueprint/LANDING.md`), step 2: `Lemma35.lean`'s `ChainData.fillCover` field is
being widened from the single-generator `⋃ n, fill i i₀ ε n` to `{z | GenClosure S X z}`,
which needs `GenClosure` in scope at `Lemma35.lean` — the reason for the move.
-/

namespace Nivat.Colle37

open Nivat Nivat.Colle

/-- The sites forced from a known set `D` by repeated `S`-generation: `base` records the
sites of `D`, and `step` is one application of the generating property of `S` at a
translate `w` of the window. -/
inductive GenClosure (S : Finset (ℤ × ℤ)) (D : Set (ℤ × ℤ)) : ℤ × ℤ → Prop
  | base {z : ℤ × ℤ} (hz : z ∈ D) : GenClosure S D z
  | step {a w : ℤ × ℤ} (ha : a ∈ S) (hconv : LatticeConvex (S.erase a))
      (h : ∀ b ∈ S.erase a, GenClosure S D (b + w)) : GenClosure S D (a + w)

/-- **Colle, Claim 3.7, Step 3.** Two members of the orbit closure that agree on `D` agree
on every site forced from `D` by the generating set `S`.  This is the paper's
"since `S_φ` is an η-generating set, we may enlarge the set where `ϑ` and `x̂_per`
coincide", proved in full. -/
theorem agree_on_genClosure {A : Type*} {η : Config A} {S : Finset (ℤ × ℤ)}
    (hS : IsGeneratingSet η S) {D : Set (ℤ × ℤ)} {x y : Config A}
    (hx : x ∈ orbitClosure η) (hy : y ∈ orbitClosure η)
    (hD : ∀ z ∈ D, x z = y z) : ∀ z, GenClosure S D z → x z = y z := by
  intro z hz
  induction hz with
  | base hz => exact hD _ hz
  | @step a w ha hconv _ ih =>
      obtain ⟨-, -, hgen⟩ := hS
      obtain ⟨-, hforce⟩ := hgen a ha hconv
      exact hforce (T w x) (T_mem_of_mem_orbitClosure hx w)
        (T w y) (T_mem_of_mem_orbitClosure hy w) (fun b hb => ih b hb)

end Nivat.Colle37

#print axioms Nivat.Colle37.agree_on_genClosure
