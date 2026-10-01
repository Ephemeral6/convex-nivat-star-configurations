/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.SweptSeed
import Nivat.External.Colle.MaximalEnveloped

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# L3's `covers` obligation, with `enum` eliminated

`Nivat.Colle43.SweptSweepData` (`SweptSeed.lean:151-174`) carries three fields that exist only
to run the sweep: `enum : ℕ → ℕ → ℤ × ℤ`, `window`, and
`covers : K ⊆ sweptSeed B u' t₁ h ∪ (⋃ i, Set.range (enum i))`.  This file removes all three
and replaces them by the single obligation

```
covers : K ⊆ genClosure S a (sweptSeed B u' t₁ h)
```

with `genClosure` the already-landed fill of `Nivat.MaxEnv` (`MaximalEnveloped.lean:694`).

## Why this is a reduction and not a re-encoding

Two facts, both proved below and both `sorry`-free:

* **Sufficiency** (§2, §3).  `genClosure` alone already drives the sweep: `agree_at_of_generatesAt`
  (`Claim43.lean:296`) is *exactly* one `genFill` step, so agreement on `D` propagates to all of
  `genClosure S a D` by a bare induction on the fill index
  (`agree_on_genClosure_of_generatesAt`).  No enumeration, no lexicographic bookkeeping.
  `hsweep_of_sweptCoverData` (§3) then reproduces the conclusion of
  `hsweep_of_sweptSweepData` (`SweptSeed.lean:212-218`) **verbatim**, so it is a drop-in at the
  `case1_sweep` call site (`RegionSteps.lean:1155-1166`).

* **No content is lost** (§4).  `SweptSweepData.toCoverData` converts every old datum into a new
  one: `window` forces `⋃ i, Set.range (enum i) ⊆ genClosure S a (sweptSeed …)`
  (`enum_mem_genClosure_of_window`), and the seed is inside `genClosure` outright
  (`subset_genClosure`), so the old `covers` implies the new one.  Hence the new obligation is
  **weaker than or equal to** the old pair `window ∧ covers` — anything that discharged L3 before
  still discharges it, and the converse direction is not needed.

⚠ The converse is *false in general* and is not claimed: `genClosure S a D` can be strictly
bigger than any single `seed ∪ ⋃ range enum` chosen in advance.  That asymmetry is the point —
the new obligation is the one with the smaller proof burden.

⚠ `Nivat.MaxEnv.genClosure` (used here) and `Nivat.Colle37.GenClosure`
(`Claim37.lean:288`, an inductive predicate) are **different objects**: the latter lets the
distinguished point `a` range over all of `S` and carries a `LatticeConvex (S.erase a)` side
condition, and its agreement lemma `Nivat.Colle37.agree_on_genClosure` (`Claim37.lean:297`)
consequently needs the full `IsGeneratingSet η S`.  `SweptSweepData` only carries
`GeneratesAt η S a` for one fixed `a`, which is why §2 proves a new lemma for the fixed-`a`
fill rather than reusing Claim 3.7's.  See `blueprint/NOTATION.md` before conflating them.

## What this file does **not** close

`case1_sweep` (`RegionSteps.lean:1077`) stays open.  §5 reduces the surviving obligation one
step further, to a *cone* statement with an explicit band hypothesis, but the band hypothesis
`hband` has no producer here — it is the same open geometric content that
`window_of_box`'s `hbase` (`SweptSeed.lean:463`) isolates, now stated without any `enum`.
-/

namespace Nivat.L3Cover

open Nivat Nivat.MaxEnv Nivat.Colle Nivat.Colle41 Nivat.Colle43

/-! ## §1  One fill step is one sweep step -/

/-- **Agreement propagates along `genClosure`.**

This is the fixed-`a` analogue of `Nivat.Colle37.agree_on_genClosure` (`Claim37.lean:297`),
with `GeneratesAt η S a` in place of `IsGeneratingSet η S`.  The induction is on the fill index
of `Nivat.MaxEnv.genFill` (`MaximalEnveloped.lean:670`); each successor step is a single
application of `agree_at_of_generatesAt` (`Claim43.lean:296`).

This is the whole reason the `enum`/`window` bookkeeping can be dropped: `genFill`'s index
already *is* the well-founded rank that `sweep_induction` (`Claim43.lean:316`) had to rebuild by
hand out of a double enumeration. -/
theorem agree_on_genClosure_of_generatesAt {A : Type*} {η x y : Config A}
    (hx : x ∈ orbitClosure η) (hy : y ∈ orbitClosure η)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : GeneratesAt η S a)
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, x z = y z) :
    ∀ z ∈ genClosure S a D, x z = y z := by
  have key : ∀ n : ℕ, ∀ z ∈ genFill S a D n, x z = y z := by
    intro n
    induction n with
    | zero => intro z hz; exact hD z hz
    | succ n ih =>
      intro z hz
      rcases genFill_step S a D n z hz with h1 | ⟨t, rfl, hb⟩
      · exact ih z h1
      · exact agree_at_of_generatesAt hx hy hgen (D := genFill S a D n) ih t hb
  intro z hz
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
  exact key n z hn

/-! ## §2  `PeriodOn` from a `genClosure` cover -/

/-- **The replacement for `claim43_periodOn_of_sweep`** (`Claim43.lean:435`).

Same hypotheses minus `enum` and `hwin`, same conclusion, with the coverage hypothesis
`K ⊆ D ∪ (⋃ i, Set.range (enum i))` replaced by `K ⊆ genClosure S a D`.

By §4 this is a *weaker* hypothesis than the pair it replaces, so every existing
`claim43_periodOn_of_sweep` call site could be rerouted through this lemma; none is rerouted
here, because that would touch files other agents are editing. -/
theorem periodOn_of_subset_genClosure {A : Type*} {η x : Config A}
    (hx : x ∈ orbitClosure η)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : GeneratesAt η S a)
    (h' : ℤ × ℤ)
    {D : Set (ℤ × ℤ)} (hD : ∀ z ∈ D, x z = T h' x z)
    {K : Set (ℤ × ℤ)} (hK : K ⊆ genClosure S a D) :
    PeriodOn x K h' :=
  periodOn_of_agree_T fun z hz =>
    agree_on_genClosure_of_generatesAt hx (T_mem_of_mem_orbitClosure hx h') hgen hD z (hK hz)

/-! ## §3  The `enum`-free sweep datum -/

/-- **`SweptSweepData` with `enum`/`window`/`covers` collapsed to one subset condition.**

Field-for-field identical to `Nivat.Colle43.SweptSweepData` (`SweptSeed.lean:151-174`) except
that the last three fields are replaced by the single

    covers : K ⊆ genClosure S a (sweptSeed B u' t₁ h)

`SweptSweepData.toCoverData` (§4) builds one of these from any `SweptSweepData`, so nothing that
used to be provable stopped being provable. -/
structure SweptCoverData {A : Type*} (η x : Config A) (u u' : ℤ × ℤ)
    (R : Set (ℤ × ℤ)) (B : Finset (ℤ × ℤ)) (t₁ : ℤ) (q : ℕ) where
  K : Set (ℤ × ℤ)
  subset_R : K ⊆ R
  isRegion : IsRegion K u u'
  nonempty : K.Nonempty
  t₀ : ℕ
  t₀_pos : 0 < t₀
  S : Finset (ℤ × ℤ)
  a : ℤ × ℤ
  generates : GeneratesAt η S a
  /-- The period of `x|ℛ` parallel to `ℓ` (`b3_colle2.txt:684`); in `case1_sweep` this is
  `c • u`, supplied by `hRper`.  Same field as `SweptSweepData.h`. -/
  h : ℤ × ℤ
  seed_subset_R : sweptSeed B u' t₁ h ⊆ R
  h_periodOn_R : ∀ z ∈ R, z + h ∈ R → x (z + h) = x z
  covers : K ⊆ genClosure S a (sweptSeed B u' t₁ h)

/-- **`hsweep` from a `SweptCoverData`.**  The statement is *verbatim* that of
`hsweep_of_sweptSweepData` (`SweptSeed.lean:212-218`) — same binders, same conclusion — so this
is a drop-in replacement at the `case1_sweep` call site. -/
theorem hsweep_of_sweptCoverData {A : Type*} {η x : Config A} (hx : x ∈ orbitClosure η)
    {u u' : ℤ × ℤ} {R : Set (ℤ × ℤ)} {B : Finset (ℤ × ℤ)} {t₁ : ℤ} {q : ℕ}
    (d : SweptCoverData η x u u' R B t₁ q)
    (hqper : ∀ g ∈ B, ∀ t : ℤ, t₁ ≤ t → x (g + (t + (q : ℤ)) • u') = x (g + t • u')) :
    ∃ K : Set (ℤ × ℤ), K ⊆ R ∧ IsRegion K u u' ∧ K.Nonempty ∧
      ∃ t₀ : ℕ, 0 < t₀ ∧ PeriodOn x K (((t₀ * q : ℕ) : ℤ) • u') := by
  refine ⟨d.K, d.subset_R, d.isRegion, d.nonempty, d.t₀, d.t₀_pos, ?_⟩
  exact periodOn_of_subset_genClosure hx d.generates (((d.t₀ * q : ℕ) : ℤ) • u')
    (agree_T_on_sweptSeed hqper d.seed_subset_R d.h_periodOn_R d.t₀) d.covers

/-! ## §4  Nothing is lost: the old datum builds the new one -/

/-- **`window` alone already puts every enumerated point in `genClosure`.**

Generalisation of `Nivat.L3win.enum_mem_genClosure_of_window`
(`tmp/L3win_window_genclosure.lean`, never landed) from the bare `halfStripFrom` to an arbitrary
seed `D`, which is what lets it apply to `sweptSeed`.  The proof is the receipt's: nested strong
induction on `(i, j)`, because `window`'s dependency order is lexicographic and
`subset_genClosure_of_rank` (`MaximalEnveloped.lean:719`) only accepts an `ℕ`-valued rank.

⚠ Direction.  This says `range enum ⊆ genClosure`, i.e. the new obligation is **implied by** the
old one.  It does not, and cannot, produce an `enum` from a `genClosure` cover. -/
theorem enum_mem_genClosure_of_window
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {D : Set (ℤ × ℤ)} {enum : ℕ → ℕ → ℤ × ℤ}
    (hwindow : ∀ i j : ℕ, ∀ z ∈ S.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' : ℕ | i' < i}, Set.range (enum i'))
          ∪ (enum i '' {j' : ℕ | j' < j})) :
    ∀ i j : ℕ, enum i j ∈ genClosure S a D := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ihi =>
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ihj =>
      have hgoal : a + (enum i j - a) ∈ genClosure S a D := by
        refine genClosure_step (S := S) (gen := a) (X := D) (t := enum i j - a) ?_
        intro b hb
        rcases hwindow i j b hb with (h1 | h2) | h3
        · exact subset_genClosure S a D h1
        · simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_range] at h2
          obtain ⟨i', hi', j'', hz''⟩ := h2
          exact hz'' ▸ ihi i' hi' j''
        · simp only [Set.mem_image, Set.mem_ofPred_eq] at h3
          obtain ⟨j', hj', hz'⟩ := h3
          exact hz' ▸ ihj j' hj'
      simpa using hgoal

/-- **The bridge.**  `window` plus `covers` gives the `genClosure` cover. -/
theorem subset_genClosure_of_window_of_covers
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {D K : Set (ℤ × ℤ)} {enum : ℕ → ℕ → ℤ × ℤ}
    (hwindow : ∀ i j : ℕ, ∀ z ∈ S.erase a,
      z + (enum i j - a) ∈
        D ∪ (⋃ i' ∈ {i' : ℕ | i' < i}, Set.range (enum i'))
          ∪ (enum i '' {j' : ℕ | j' < j}))
    (hcovers : K ⊆ D ∪ (⋃ i, Set.range (enum i))) :
    K ⊆ genClosure S a D := by
  intro z hz
  rcases hcovers hz with hzD | hzU
  · exact subset_genClosure S a D hzD
  · simp only [Set.mem_iUnion, Set.mem_range] at hzU
    obtain ⟨i, j, rfl⟩ := hzU
    exact enum_mem_genClosure_of_window hwindow i j

/-- **Every `SweptSweepData` is a `SweptCoverData`.**  So §3's obligation is weaker than or equal
to `SweptSweepData`'s `window ∧ covers`, and rerouting L3 through `SweptCoverData` cannot lose a
proof that the old route would have found. -/
def SweptSweepData.toCoverData {A : Type*} {η x : Config A} {u u' : ℤ × ℤ}
    {R : Set (ℤ × ℤ)} {B : Finset (ℤ × ℤ)} {t₁ : ℤ} {q : ℕ}
    (d : SweptSweepData η x u u' R B t₁ q) :
    SweptCoverData η x u u' R B t₁ q where
  K := d.K
  subset_R := d.subset_R
  isRegion := d.isRegion
  nonempty := d.nonempty
  t₀ := d.t₀
  t₀_pos := d.t₀_pos
  S := d.S
  a := d.a
  generates := d.generates
  h := d.h
  seed_subset_R := d.seed_subset_R
  h_periodOn_R := d.h_periodOn_R
  covers := subset_genClosure_of_window_of_covers d.window d.covers

/-! ## §5  Reducing `covers` to a cone, with the band isolated

The remaining obligation is `K ⊆ genClosure S a (sweptSeed B u' t₁ h)`.  This section discharges
it from the same two-dimensional window hypothesis `hSbox` that `window_of_box`
(`SweptSeed.lean:463`) uses, plus one band hypothesis — and, unlike `window_of_box`, needs **no**
`hrow`, because there are no rows any more.
-/

/-- **The quarter-cone `{g₀ + i·w' + j·w : i, j ∈ ℕ}` is generated from the band behind it.**

`hSbox` is *verbatim* `window_of_box`'s (`SweptSeed.lean:463`): every punctured window point sits
in the `N × M` box behind `a` in directions `w`, `w'`.  `hband` replaces that lemma's `hrow` *and*
`hbase` at once: it asks the seed to contain the L-shaped band of width `M` below the cone and
width `N` to its left.

The `ℕ`-rank that makes this work — and that could not work for `window`, see
`enum_mem_genClosure_of_window` — is `ρ (i, j) = i + j`: a window point at `(i - m, j - k)` has
`k + m ≥ 1`, so its rank drops strictly, *without* any lexicographic refinement.  The double
enumeration was never needed; only `window`'s formulation forced it.

⚠ `hband` has **no producer**.  It is the same open geometric content as `window_of_box`'s
`hbase`, and the `p ≥ -M`, `q ≥ -N` bounds are load-bearing for the same reason recorded there:
`Nivat.L3win.no_hbase_of_transverse` (`tmp/L3win_hbase_refute.lean`) refutes the doubly-infinite
form whenever `det u' w ≠ 0`.  Stated as a hypothesis, not smuggled into the conclusion. -/
theorem cone_subset_genClosure_of_box
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {w w' : ℤ × ℤ} {N M : ℕ}
    (hSbox : ∀ b ∈ S.erase a, ∃ k m : ℕ, k ≤ N ∧ m ≤ M ∧ 1 ≤ k + m ∧
      b = a - (k : ℤ) • w - (m : ℤ) • w')
    {D : Set (ℤ × ℤ)} {g₀ : ℤ × ℤ}
    (hband : ∀ p q : ℤ, -(M : ℤ) ≤ p → -(N : ℤ) ≤ q → (p < 0 ∨ q < 0) →
      g₀ + p • w' + q • w ∈ D) :
    ∀ i j : ℕ, g₀ + (i : ℤ) • w' + (j : ℤ) • w ∈ genClosure S a D := by
  have key : ∀ n i j : ℕ, i + j = n →
      g₀ + (i : ℤ) • w' + (j : ℤ) • w ∈ genClosure S a D := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i j hij
      have hgoal : a + (g₀ + (i : ℤ) • w' + (j : ℤ) • w - a) ∈ genClosure S a D := by
        refine genClosure_step (S := S) (gen := a) (X := D)
          (t := g₀ + (i : ℤ) • w' + (j : ℤ) • w - a) ?_
        intro b hb
        obtain ⟨k, m, hkN, hmM, hkm, rfl⟩ := hSbox b hb
        have heq : (a - (k : ℤ) • w - (m : ℤ) • w') + (g₀ + (i : ℤ) • w' + (j : ℤ) • w - a)
            = g₀ + ((i : ℤ) - (m : ℤ)) • w' + ((j : ℤ) - (k : ℤ)) • w := by
          module
        rw [heq]
        by_cases hm : m ≤ i
        · by_cases hk : k ≤ j
          · -- Both indices stay in the cone; the rank `i + j` drops because `k + m ≥ 1`.
            have e1 : (i : ℤ) - (m : ℤ) = ((i - m : ℕ) : ℤ) := by omega
            have e2 : (j : ℤ) - (k : ℤ) = ((j - k : ℕ) : ℤ) := by omega
            rw [e1, e2]
            exact ih ((i - m) + (j - k)) (by omega) (i - m) (j - k) rfl
          · -- Reaches left of the cone, by at most `N`.
            exact subset_genClosure S a D
              (hband _ _ (by omega) (by omega) (Or.inr (by omega)))
        · -- Reaches below the cone, by at most `M`.
          exact subset_genClosure S a D
            (hband _ _ (by omega) (by omega) (Or.inl (by omega)))
      simpa using hgoal
  exact fun i j => key (i + j) i j rfl

/-- **`SweptCoverData.covers`, discharged for a cone-shaped `K`.**  The form the L3 call site
actually needs: `K` is contained in the quarter-cone, the window fits in the box, and the seed
contains the band. -/
theorem covers_of_box_of_cone
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {w w' : ℤ × ℤ} {N M : ℕ}
    (hSbox : ∀ b ∈ S.erase a, ∃ k m : ℕ, k ≤ N ∧ m ≤ M ∧ 1 ≤ k + m ∧
      b = a - (k : ℤ) • w - (m : ℤ) • w')
    {D K : Set (ℤ × ℤ)} {g₀ : ℤ × ℤ}
    (hband : ∀ p q : ℤ, -(M : ℤ) ≤ p → -(N : ℤ) ≤ q → (p < 0 ∨ q < 0) →
      g₀ + p • w' + q • w ∈ D)
    (hKcone : K ⊆ {z : ℤ × ℤ | ∃ i j : ℕ, z = g₀ + (i : ℤ) • w' + (j : ℤ) • w}) :
    K ⊆ genClosure S a D := by
  intro z hz
  obtain ⟨i, j, rfl⟩ := hKcone hz
  exact cone_subset_genClosure_of_box hSbox hband i j

/-- **End to end.**  `hsweep` for a cone-shaped `K`, from the box window and the band, with no
`enum` anywhere.  This is the statement L3 should aim at; what remains open is `hband` (and, as
before, the `hSbox` producer — `Nivat.L3win.hSbox_of_corner`, `tmp/L3win_hSbox_cramer.lean`,
still has no call-site producer). -/
theorem hsweep_of_box_of_cone {A : Type*} {η x : Config A} (hx : x ∈ orbitClosure η)
    {u u' : ℤ × ℤ} {R : Set (ℤ × ℤ)} {B : Finset (ℤ × ℤ)} {t₁ : ℤ} {q : ℕ}
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : GeneratesAt η S a)
    {w w' : ℤ × ℤ} {N M : ℕ}
    (hSbox : ∀ b ∈ S.erase a, ∃ k m : ℕ, k ≤ N ∧ m ≤ M ∧ 1 ≤ k + m ∧
      b = a - (k : ℤ) • w - (m : ℤ) • w')
    {h : ℤ × ℤ} {g₀ : ℤ × ℤ}
    (hseedR : sweptSeed B u' t₁ h ⊆ R)
    (hper : ∀ z ∈ R, z + h ∈ R → x (z + h) = x z)
    (hband : ∀ p q : ℤ, -(M : ℤ) ≤ p → -(N : ℤ) ≤ q → (p < 0 ∨ q < 0) →
      g₀ + p • w' + q • w ∈ sweptSeed B u' t₁ h)
    {K : Set (ℤ × ℤ)} (hKR : K ⊆ R) (hKregion : IsRegion K u u') (hKne : K.Nonempty)
    (hKcone : K ⊆ {z : ℤ × ℤ | ∃ i j : ℕ, z = g₀ + (i : ℤ) • w' + (j : ℤ) • w})
    {t₀ : ℕ} (ht₀ : 0 < t₀)
    (hqper : ∀ g ∈ B, ∀ t : ℤ, t₁ ≤ t → x (g + (t + (q : ℤ)) • u') = x (g + t • u')) :
    ∃ K : Set (ℤ × ℤ), K ⊆ R ∧ IsRegion K u u' ∧ K.Nonempty ∧
      ∃ t₀ : ℕ, 0 < t₀ ∧ PeriodOn x K (((t₀ * q : ℕ) : ℤ) • u') :=
  hsweep_of_sweptCoverData hx
    { K := K
      subset_R := hKR
      isRegion := hKregion
      nonempty := hKne
      t₀ := t₀
      t₀_pos := ht₀
      S := S
      a := a
      generates := hgen
      h := h
      seed_subset_R := hseedR
      h_periodOn_R := hper
      covers := covers_of_box_of_cone hSbox hband hKcone }
    hqper


/-! ## §6  Non-vacuity of §5

⚠ `hband` is an open geometric obligation with no producer (§5), so the risk that
`cone_subset_genClosure_of_box` is *vacuously* true — `hSbox ∧ hband` unsatisfiable, as happened
to `window_of_runs`'s `hSrun` (`no_hSrun_of_nonCollinear`, `SweptSeed.lean:404`) — is real and
has to be discharged by exhibiting a model.  This section does, with a **genuine**
`sweptSeed`/`genClosure`, and also checks the conclusion is not already contained in the seed.
-/

private def nvS : Finset (ℤ × ℤ) := {(0, 0), (-1, 0)}
private def nvB : Finset (ℤ × ℤ) := {(-1, 0)}

/-- `S ∖ {a} = {(-1,0)}` sits in the `0 × 1` box behind `a = (0,0)`: `hSbox` with `N = 0`,
`M = 1`, `w = (0,1)`, `w' = (1,0)`. -/
private theorem nv_hSbox : ∀ b ∈ nvS.erase ((0, 0) : ℤ × ℤ),
    ∃ k m : ℕ, k ≤ 0 ∧ m ≤ 1 ∧ 1 ≤ k + m ∧
      b = ((0, 0) : ℤ × ℤ) - (k : ℤ) • ((0, 1) : ℤ × ℤ) - (m : ℤ) • ((1, 0) : ℤ × ℤ) := by
  intro b hb
  have hb' : b = ((-1, 0) : ℤ × ℤ) := by
    simp only [nvS, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hb
    tauto
  exact ⟨0, 1, le_refl 0, le_refl 1, by omega, by simp [hb']⟩

/-- The band behind the cone really is inside the seed: `hband` with the same `N = 0`, `M = 1`.
The only band points are `(-1, q)` for `q ≥ 0`, and those are the half-strip over `B = {(-1,0)}`
in direction `u' = (0,1)` from `t₁ = 0`. -/
private theorem nv_hband : ∀ p q : ℤ, -((1 : ℕ) : ℤ) ≤ p → -((0 : ℕ) : ℤ) ≤ q →
    (p < 0 ∨ q < 0) →
    ((0, 0) : ℤ × ℤ) + p • ((1, 0) : ℤ × ℤ) + q • ((0, 1) : ℤ × ℤ)
      ∈ sweptSeed nvB ((0, 1) : ℤ × ℤ) 0 ((0, 0) : ℤ × ℤ) := by
  intro p q hp hq hlt
  have hp' : p = -1 := by omega
  refine ⟨0, ⟨(-1, 0), by simp [nvB], q, hq, ?_⟩⟩
  simp [hp']

/-- **The §5 hypotheses are simultaneously satisfiable, and their conclusion is not vacuous**:
`(1,1)` is in the generated closure but not in the seed it is generated from. -/
theorem cone_hypotheses_nonvacuous :
    ((1, 1) : ℤ × ℤ) ∈
      genClosure nvS ((0, 0) : ℤ × ℤ) (sweptSeed nvB ((0, 1) : ℤ × ℤ) 0 ((0, 0) : ℤ × ℤ)) ∧
    ((1, 1) : ℤ × ℤ) ∉ sweptSeed nvB ((0, 1) : ℤ × ℤ) 0 ((0, 0) : ℤ × ℤ) := by
  constructor
  · have h := cone_subset_genClosure_of_box (N := 0) (M := 1) (g₀ := ((0, 0) : ℤ × ℤ))
      nv_hSbox nv_hband 1 1
    simpa [Prod.ext_iff] using h
  · rintro ⟨ι, g, hg, t, -, heq⟩
    simp only [nvB, Finset.mem_singleton] at hg
    subst hg
    simp [Prod.ext_iff] at heq
end Nivat.L3Cover
