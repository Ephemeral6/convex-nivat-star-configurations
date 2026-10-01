/-
Lane `lane-fillcover`, 2026-09-23.  `tmp/wip/`, 0 `sorry`.

# `fillCover` binder of `ChainDataGeom.ofPartsExhaustsInter`: reduction and status

Target: the `fillCover` binder of `Nivat.Colle35.ChainDataGeom.ofPartsExhaustsInter`
(`ChainExhaustInter.lean`), feeding `exists_chainData`
(`RegionSteps.lean:1166`) via the wiring skeleton `tmp/wip/LeafAAssemble.lean:1064`.

## What is already on record (硬规矩 3: read before writing)

`tmp/wip/lane-cd-cw-fillcover.lean` (lane `lane-cd-cw`, 2026-09-23, 0 `sorry`,
`#print axioms` clean) already reduces the binder to a single local hypothesis `hstep`
via `subset_genClosure_of_covector` / `exists_lex_covector` / `fillCover_of_collar_step`.
That file is **not imported here** (tmp/wip files are not lake modules reachable by
`import`), but its route is re-derived below, self-contained, and pushed one step
further: specialised to the actual call pattern `i₀ ≤ i` (`ChainExhaustInter.lean`),
using `AhatMono` to show the target of `hstep`'s window-neighbour clause collapses from
`X ∪ Y_i` to `Y_i` outright, and its "already done" clause keeps the genuine room `X`
supplies via `Y_{i₀}`.  A dozen further `tmp/wip/lane-cd-*` files attack pieces of the
remaining local geometric condition (`bottom`-driven ray structure, corner/width
lemmas); none of them, as of this file's writing, discharges `hstep` outright.  This file
does not re-litigate that search; it records the exact reduction and the exact
remaining obligation.

## §0. What is landed here (0 sorry)

* `shellInter_mono_left` — `shellInter` is monotone in its first argument (missing
  companion to `ShellMink.lean:518`'s `shellInter_subset_right` / `subset_shellInter`).
* `subset_genClosure_of_covector`, `exists_lex_covector` — re-derivation of
  `lane-cd-cw-fillcover.lean §3` (same statements, reproved).
* `fillCover_of_collar_step` — the `fillCover` binder from one local hypothesis `hstep`
  quantified over unconstrained `i₀` (matches `lane-cd-cw-fillcover.lean`'s
  `fillCover_of_collar_step` up to the trivial `∀ i i₀ ε, i₀ ≤ i → …` vs `∀ i i₀ ε, …`
  strengthening the caller already accepts).
* `fillCover_of_local_step` — **the further reduction.**  Under `i₀ ≤ i` and `AhatMono`,
  `X_i,i₀ ⊆ Y_i` (`X_subset_Y`), so the window-neighbour clause's target `X ∪ Y_i`
  collapses to `Y_i` alone; the theorem takes `hstep` in that simplified form.

## §1. What is NOT landed: the exact remaining obligation

`fillCover_of_local_step`'s hypothesis `hstepLocal`:

    ∀ i i₀ ε, i₀ ≤ i → ∀ z ∈ ShellMink.shellInter (Ahat i)
        (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w,
      z ∈ Ahat i ∪ ShellMink.shellInter (Ahat i₀)
            (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w ∨
      ∀ b ∈ S.erase gen, z + (b - gen) ∈
        ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w

is exactly what remains.  Unfolding the disjunction: writing `z = g + t • w` with
`g ∈ Ahat i` (`t : ℕ`, the `reachSet` witness), the two `FaceBlock.edge'` cases at
`gen = F.a'` split it further:

* **edge case** (`b = a' - j•v`, `1 ≤ j ≤ F.r`): needs `z - j • vJ ∈ Ahat i ∪ Y_{i₀}` or
  `z - j • vJ ∈ Y_i` — a *backward* translate along the face direction, for which nothing
  in `Ahat`'s abstract hypothesis list (`AhatMono, hfin, hhp, hswept, ahat_nonempty,
  envB, maxA, subBA, subAB`) gives traction; only `rec_vJ_of_bottom`'s *forward* closure
  (`ell_side_of_exhausts`'s own dependency, `+vJ` only) is available off `bottom`.
* **general case** (`dot nJ (b - a') ≥ 1`): needs the translate to land back in the same
  reachSet/shell structure; `AhatHeight.lean`'s `mul_le_of_mem_shellInter` /
  `transverse_of_mem_shellInter` (`Nivat/External/Colle/AhatHeight.lean:126,143`) bound
  the sweep depth `t` by a quantity attached to `B i` but do not by themselves place
  `z + (b - gen)` back inside `Y_i` — that needs `maxA`, which nothing here uses yet.

Both cases plausibly resolve through the `bottom` hypothesis (`ChainExhaustInter.lean`),
whose third clause `∀ b ∈ S, ∀ k, L ≤ k → z₀ + k•vJ + (b - F.a) ∈ reachSet Â∞
vJ1` is verbatim the "window neighbour lands back in the sweep" statement `hstepLocal`
needs, but for a *specific* ray `z₀ + k•vJ` (`bottom`'s witness) rather than the general
point `z ∈ Y_i`.  Bridging "every `z ∈ Y_i \ (Ahat i ∪ Y_{i₀})` is `bottom`'s ray point at
some `k`" is the missing geometric lemma; it is not attempted here (硬规矩 5: this is the
quantifier that would need to be added and justified against `bottom`'s exact shape, not
invented ad hoc).

## Two honest outcomes, applied

Outcome 1 (a 0-sorry theorem concluding `fillCover` verbatim) is **not** reached.
`fillCover_of_local_step` compiles with 0 `sorry` and is a real strengthening of the
`lane-cd-cw-fillcover.lean` reduction (simpler target set), but its own hypothesis
`hstepLocal` is exactly as hard as the original `fillCover` binder was believed to be —
no counterexample is claimed either.  Reported as instructed: "the reduction of the
inductive step to an exact Lean type."

Does NOT import `RegionSteps`/`ColleRegion`/`Case2WindowProbe`/`NfpLPreamble` (red line).
-/
import Nivat.External.Colle.ShellMink
import Nivat.External.Colle.ChainMax

set_option autoImplicit false

namespace Nivat.LaneFillCover

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35

/-! ## §0a. The missing monotonicity companion for `shellInter` -/

/-- **`shellInter` is monotone in its first (swept-set) argument.**  Companion to
`ShellMink.shellInter_subset_right` / `ShellMink.subset_shellInter`
(`ShellMink.lean:513,517`), which fix the first argument. -/
theorem shellInter_mono_left {A A' Ainf : Set (ℤ × ℤ)} (h : A ⊆ A') (w : ℤ × ℤ) :
    ShellMink.shellInter A Ainf w ⊆ ShellMink.shellInter A' Ainf w :=
  Set.inter_subset_inter_left _ (ShellMink.reachSet_mono h w)

/-! ## §1. The well-founded-rank criterion for `genClosure`, from a `FaceBlock` covector

Re-derivation of `tmp/wip/lane-cd-cw-fillcover.lean §3` (lane `lane-cd-cw`), self-contained
so this file compiles standalone. -/

/-- **`genClosure` from a single rank covector.**  If `gen` strictly minimises `dot n'`
over `S`, `dot n'` is bounded above on `Y`, and every point of `Y` is either already in
`X` or has all its `S`-window neighbours in `X ∪ Y`, then `Y ⊆ genClosure S gen X`.
Paper: `b3_colle2.txt:530`, the "by induction" step. -/
theorem subset_genClosure_of_covector
    {S : Finset (ℤ × ℤ)} {gen n' : ℤ × ℤ} {X Y : Set (ℤ × ℤ)} {C : ℤ}
    (hbdd : ∀ z ∈ Y, dot n' z ≤ C)
    (hgen : ∀ b ∈ S.erase gen, dot n' gen < dot n' b)
    (hstep : ∀ z ∈ Y, z ∈ X ∨ ∀ b ∈ S.erase gen, z + (b - gen) ∈ X ∪ Y) :
    Y ⊆ genClosure S gen X := by
  classical
  have hlin : ∀ u v : ℤ × ℤ, dot n' (u + (v - gen)) = dot n' u + (dot n' v - dot n' gen) := by
    intro u v
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
    ring
  refine subset_genClosure_of_rank (fun z => (C + 1 - dot n' z).toNat) ?_
  intro z hz
  rcases hstep z hz with hx | h
  · exact Or.inl hx
  · refine Or.inr ⟨z - gen, by abel, fun b hb => ?_⟩
    have hrw : b + (z - gen) = z + (b - gen) := by abel
    rw [hrw]
    have h1 : dot n' gen < dot n' b := hgen b hb
    have h2 : dot n' (z + (b - gen)) = dot n' z + (dot n' b - dot n' gen) := hlin z b
    have h3 : dot n' z ≤ C := hbdd z hz
    rcases h b hb with hx | hy
    · exact Or.inl hx
    · exact Or.inr ⟨hy, by omega⟩

/-- **The rank covector exists for `gen = F.a'`, from `FaceBlock.lex'` alone.**
`n' := K • nJ - vJ` with `K := 1 + max_{b ∈ S} (dot vJ b - dot vJ a')` linearises the
lexicographic order `(dot nJ ·, -dot vJ ·)` that `lex'` (`ANormal.lean:601`) pins `a'`
at. -/
theorem exists_lex_covector {S : Finset (ℤ × ℤ)} {nJ vJ : ℤ × ℤ} (F : FaceBlock S nJ vJ) :
    ∃ n' : ℤ × ℤ, ∀ b ∈ S.erase F.a', dot n' F.a' < dot n' b := by
  classical
  have hSne : S.Nonempty := ⟨F.a', F.a'_mem⟩
  obtain ⟨M, hMle⟩ : ∃ M : ℤ, ∀ b ∈ S, dot vJ b - dot vJ F.a' ≤ M :=
    ⟨S.sup' hSne (fun b => dot vJ b - dot vJ F.a'),
      fun b hb => Finset.le_sup' (fun b => dot vJ b - dot vJ F.a') hb⟩
  have hM0 : (0 : ℤ) ≤ M := by
    have := hMle F.a' F.a'_mem
    omega
  have hdot : ∀ b : ℤ × ℤ, dot ((1 + M) • nJ - vJ) b = (1 + M) * dot nJ b - dot vJ b := by
    intro b
    simp only [dot, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  refine ⟨(1 + M) • nJ - vJ, fun b hb => ?_⟩
  have hbS : b ∈ S := Finset.mem_of_mem_erase hb
  have hMb := hMle b hbS
  rw [hdot, hdot]
  rcases F.lex' b hb with hlt | ⟨heq, hv⟩
  · rw [dot_neg_left, dot_neg_left] at hlt
    have h1 : dot nJ F.a' + 1 ≤ dot nJ b := by omega
    nlinarith [hM0, hMb, h1]
  · rw [dot_neg_left, dot_neg_left] at heq
    have heq' : dot nJ b = dot nJ F.a' := by omega
    rw [heq']
    omega

/-! ## §2. `fillCover` from the one-step collar condition (unconstrained `i₀`) -/

/-- **`fillCover` from the one-step collar condition.**  Conclusion is character-for-
character `ChainDataGeom.ofPartsExhaustsInter`'s `fillCover` binder minus the `i₀ ≤ i →`
guard (a strengthening the caller does not need but which is free to prove: `hstep` is
simply not asked to hold outside `i₀ ≤ i`).  Matches `lane-cd-cw-fillcover.lean`'s lemma
of the same name. -/
theorem fillCover_of_collar_step
    {S : Finset (ℤ × ℤ)} {gen nJ vJ vJ1 w : ℤ × ℤ} {cJ : ℤ} {Ahat : ℕ → Set (ℤ × ℤ)}
    (hfin : ∀ i, (Ahat i).Finite)
    (hsweepW : dot nJ w < 0)
    (F : FaceBlock S nJ vJ) (gen_eq : gen = F.a')
    (hstep : ∀ i i₀ ε, ∀ z ∈ ShellMink.shellInter (Ahat i)
          (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w,
        z ∈ Ahat i ∪ ShellMink.shellInter (Ahat i₀)
              (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w ∨
        ∀ b ∈ S.erase gen,
          z + (b - gen) ∈
            (Ahat i ∪ ShellMink.shellInter (Ahat i₀)
              (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w) ∪
            ShellMink.shellInter (Ahat i)
              (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w) :
    ∀ i i₀ ε,
      ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w ⊆
        ⋃ n, genFill S gen (Ahat i ∪
          ShellMink.shellInter (Ahat i₀)
            (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w) n := by
  classical
  obtain ⟨n', hn'⟩ := exists_lex_covector F
  rw [gen_eq]
  intro i i₀ ε
  have hYsub : ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w ⊆
      MaxEnv.shell (Ahat i) w nJ cJ ε := by
    rintro z ⟨⟨g, hg, t, rfl⟩, hsh⟩
    obtain ⟨-, -, -, -, hlev⟩ := hsh
    exact ⟨g, hg, t, rfl, hlev⟩
  have hYfin : (ShellMink.shellInter (Ahat i)
      (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w).Finite :=
    (MaxEnv.shell_finite (hfin i) hsweepW).subset hYsub
  obtain ⟨C, hC⟩ : ∃ C : ℤ, ∀ z ∈ ShellMink.shellInter (Ahat i)
      (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w, dot n' z ≤ C := by
    obtain ⟨C, hC⟩ := (hYfin.image (fun z => dot n' z)).bddAbove
    exact ⟨C, fun z hz => hC ⟨z, hz, rfl⟩⟩
  have hgen' : ∀ b ∈ S.erase F.a', dot n' F.a' < dot n' b := hn'
  exact subset_genClosure_of_covector (S := S) (gen := F.a') (n' := n') (C := C)
    hC hgen' (by rw [← gen_eq]; exact hstep i i₀ ε)

/-! ## §3. The further reduction: `i₀ ≤ i` collapses the neighbour target to `Y_i` -/

/-- **`Ahat i` sits inside its own collar `Y_i`.**  `t = 0` for `reachSet`, and
`subset_shell` off `hhp` for the level cut. -/
theorem Ahat_subset_shellInter {Ahat : ℕ → Set (ℤ × ℤ)} {nJ vJ1 w : ℤ × ℤ} {cJ : ℤ} {ε : ℕ} {i : ℕ}
    (hhp : ∀ i, Ahat i ⊆ halfPlaneGE nJ cJ) :
    Ahat i ⊆ ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w :=
  ShellMink.subset_shellInter
    (fun z hz => subset_shell ε (Set.iUnion_subset hhp) (Set.subset_iUnion Ahat i hz)) w

/-- **`i₀ ≤ i` collapses `X` into `Y_i`.**  With `AhatMono` and `hhp`,
`Ahat i ∪ Y_{i₀} ⊆ Y_i` — the seed `Y_{i₀}` never sticks out of the current collar. -/
theorem X_subset_Y {Ahat : ℕ → Set (ℤ × ℤ)} {nJ vJ1 w : ℤ × ℤ} {cJ : ℤ} {ε : ℕ} {i i₀ : ℕ}
    (AhatMono : ∀ i j, i ≤ j → Ahat i ⊆ Ahat j)
    (hhp : ∀ i, Ahat i ⊆ halfPlaneGE nJ cJ) (hi : i₀ ≤ i) :
    Ahat i ∪ ShellMink.shellInter (Ahat i₀) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w ⊆
      ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w :=
  Set.union_subset (Ahat_subset_shellInter hhp) (shellInter_mono_left (AhatMono i₀ i hi) w)

/-- **`fillCover` from the `i₀ ≤ i`-specialised local step.**  Same conclusion as
`ChainExhaustInter.lean`'s `fillCover` binder verbatim (with the `i₀ ≤ i →` guard kept,
matching the real call site).  `hstepLocal`'s window-neighbour clause targets `Y_i` alone
(not `X ∪ Y_i`) — sound because `X_subset_Y` shows they agree once `i₀ ≤ i`; its
"already done" clause keeps the genuine room `X = Ahat i ∪ Y_{i₀}` supplies.  **This is
the exact remaining obligation** (module docstring §1). -/
theorem fillCover_of_local_step
    {S : Finset (ℤ × ℤ)} {gen nJ vJ vJ1 w : ℤ × ℤ} {cJ : ℤ} {Ahat : ℕ → Set (ℤ × ℤ)}
    (AhatMono : ∀ i j, i ≤ j → Ahat i ⊆ Ahat j)
    (hhp : ∀ i, Ahat i ⊆ halfPlaneGE nJ cJ)
    (hfin : ∀ i, (Ahat i).Finite)
    (hsweepW : dot nJ w < 0)
    (F : FaceBlock S nJ vJ) (gen_eq : gen = F.a')
    (hstepLocal : ∀ i i₀ ε, i₀ ≤ i → ∀ z ∈ ShellMink.shellInter (Ahat i)
          (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w,
        z ∈ Ahat i ∪ ShellMink.shellInter (Ahat i₀)
              (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w ∨
        ∀ b ∈ S.erase gen,
          z + (b - gen) ∈
            ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w) :
    ∀ i i₀ ε, i₀ ≤ i →
      ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w ⊆
        ⋃ n, genFill S gen (Ahat i ∪
          ShellMink.shellInter (Ahat i₀)
            (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w) n := by
  classical
  subst gen_eq
  intro i i₀ ε hi
  obtain ⟨n', hn'⟩ := exists_lex_covector F
  have hYsub : ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w ⊆
      MaxEnv.shell (Ahat i) w nJ cJ ε := by
    rintro z ⟨⟨g, hg, t, rfl⟩, hsh⟩
    obtain ⟨-, -, -, -, hlev⟩ := hsh
    exact ⟨g, hg, t, rfl, hlev⟩
  have hYfin : (ShellMink.shellInter (Ahat i)
      (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w).Finite :=
    (MaxEnv.shell_finite (hfin i) hsweepW).subset hYsub
  obtain ⟨C, hC⟩ : ∃ C : ℤ, ∀ z ∈ ShellMink.shellInter (Ahat i)
      (MaxEnv.shell (⋃ i, Ahat i) vJ1 nJ cJ ε) w, dot n' z ≤ C := by
    obtain ⟨C, hC⟩ := (hYfin.image (fun z => dot n' z)).bddAbove
    exact ⟨C, fun z hz => hC ⟨z, hz, rfl⟩⟩
  refine subset_genClosure_of_covector (S := S) (gen := F.a') (n' := n') (C := C) hC hn' ?_
  intro z hz
  rcases hstepLocal i i₀ ε hi z hz with hzX | hzNbr
  · exact Or.inl hzX
  · exact Or.inr fun b hb => Or.inr (hzNbr b hb)

end Nivat.LaneFillCover

#print axioms Nivat.LaneFillCover.shellInter_mono_left
#print axioms Nivat.LaneFillCover.subset_genClosure_of_covector
#print axioms Nivat.LaneFillCover.exists_lex_covector
#print axioms Nivat.LaneFillCover.fillCover_of_collar_step
#print axioms Nivat.LaneFillCover.Ahat_subset_shellInter
#print axioms Nivat.LaneFillCover.X_subset_Y
#print axioms Nivat.LaneFillCover.fillCover_of_local_step
