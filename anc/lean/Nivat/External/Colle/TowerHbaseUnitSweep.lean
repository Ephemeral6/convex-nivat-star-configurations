/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ShellLine

/-!
# The sweep step size `dot nJ vJ1 = -1`, and `bottom`'s conjuncts 1–3

`ChainDataGeomParts.bottom` (`ChainPartsFeed.lean:288-294`) has four conjuncts.  Conjuncts 1–3
(`:289`, `:290`, `:291-292`) are discharged here from

* a translate of `S` inside `Â_∞`,
* `hhp` (field `hhp`, `ChainPartsFeed.lean:220`),
* `rec_vJ`,
* and **one integer equation**, `dot nJ vJ1 = -1`.

Conjunct 4 (`:293-294`) is *not* touched here; it belongs to lane-hole3-nlmax.
`bottom_conj123` exports the ray-level fact `dot nJ (z₀ + k • vJ) = cJ - ε - 1` alongside the
three conjuncts, because that is what conjunct 4 is stated against.

⚠ **Anchoring.**  `bottom`'s conjuncts 1–2 have no verbatim source sentence:
`b3_colle2.txt:518-520` is verbatim `shellEnv`, not `bottom` (lane-hole3-nlmax reports, §55).
So the docstrings below anchor to the *field*, not to `b3_colle2.txt`, and say so rather than
inventing a line number.

## Why `-1` and not just `< 0`

The chain gives only `hsweep : dot nJ vJ1 < 0` (field `hsweep`, `ChainPartsFeed.lean:218`), and
`< 0` is not enough.  Two independent main-repo counter-instances:

* `Nivat.Colle35.not_bottom_of_shell_data` (`ANormal.lean:843`) — a counter-model at step `-2`.
* `Nivat.Colle35.not_isLatticeConvexRegion_shell_of_formula` (`RegionClaim411.lean:854`), whose
  conclusion asserts `Primitive vJ ∧ Primitive nJ ∧ Primitive vJ1` all three
  (`RegionClaim411.lean:859`) while its data is `ShellCx.vJC = (1,0)`
  (`RegionClaim411.lean:780`), `ShellCx.nJC = (0,1)` (`:781`), `ShellCx.vJ1C = (1,-2)` (`:782`)
  — i.e. `dot nJ vJ1 = -2` **and** `det vJ vJ1 = -2`.

Two consequences, both load-bearing for how this file is shaped:

1. **Primitivity can never force `-1`.**  `RegionClaim411.lean:854` exhibits the
   counter-instance inside the main repo, with all three vectors primitive.  So
   `unit_sweep_of_adjacent` deliberately does **not** take `Primitive vJ1`, and does not take
   `Primitive vJ` either.
2. **`dot nJ vJ1 ≠ -2` is not usable as a hypothesis for `-1`**: nothing in the data excludes
   `-3`.  §1 identifies the invariant that does the work.

## §1's content: the step size *is* the determinant

Under `dot nJ vJ = 0` and `Primitive nJ`, `dot nJ vJ1` and `det vJ vJ1` divide each other, so
`unit_sweep_iff_unimodular` holds:

```
dot nJ vJ1 = -1  ↔  det vJ vJ1 = 1 ∨ det vJ vJ1 = -1
```

So the step-size debt **is** the unimodularity of the pair `(v_{ℓ_J}, v_{ℓ_{J-1}})` — Collé's
adjacency of two consecutive chain directions — and there is no cheaper route to it.  Deriving
that adjacency is banned for this lane (standing discipline 23), so it enters as the hypothesis
`hadj` and is never proved here.

⚠ Discipline 23 names `⟪n_J, w⟫ = -1`, about the field `w` (`ChainPartsFeed.lean:236`).  Since
the 2026-09-25 ruling recorded in that field's own docstring (`ChainPartsFeed.lean:226-235`),
`w` and `vJ1` are **two** pieces of data and `w` must be transverse; the last line there,
"`vJ1 ∥ vl` … 那说的是 `vJ1`，不是 `w`", is the same distinction.  Nothing in this file
mentions `w`.

## Provenance of every hypothesis used

* `hnJ_prim : Primitive nJ` — field `nJ_prim` (`ChainPartsFeed.lean:286`).
* `hvJ_prim : Primitive vJ` — field `vJ_prim` (`ChainPartsFeed.lean:285`).
* `hperp : dot nJ vJ = 0` — field `dot_nJ_vJ` of `Nivat.Colle35.FaceBlock` (`ANormal.lean:616`),
  reached through field `F` (`ChainPartsFeed.lean:282`).
* `hsweep : dot nJ vJ1 < 0` — field `hsweep` (`ChainPartsFeed.lean:218`).
* `hhp` — field `hhp` (`ChainPartsFeed.lean:220`), after unfolding `halfPlaneGE`.
* `ha : a ∈ S` — field `a_mem` of `FaceBlock` (`ANormal.lean:600`); `a` stands for `F.a`, the
  point subtracted in conjunct 3 (`ChainPartsFeed.lean:292`).
* `hadj : det vJ vJ1 = 1 ∨ det vJ vJ1 = -1` — **no producer in the tree**.  Searched by
  conclusion type over `Nivat/**.lean`: 0 hits; the statement does not occur.  Banned for this
  lane to prove (discipline 23's neighbour), so it is a hypothesis everywhere below.
* `htile : ∀ b ∈ S, b + wS ∈ Ah` — **no producer found**.  `EnvOf ↑S`
  (`LatticeEdges.lean:2508`) unfolds to `Enveloped` (`LatticeEdges.lean:703`), an *edge*
  condition, not "covered by translates of `S`", so `envB` / `maxA` do not supply it.

⚠ **§97.**  The tile offset is `wS`, deliberately not `w`: it is unrelated to the field `w`
(`ChainPartsFeed.lean:236`).  The `w` appearing in §1 is a bound variable of an algebraic
identity, quantified over all of `ℤ × ℤ`.  No statement in this file identifies any vector
with `vJ1`.

## Main results

* `unit_sweep_of_adjacent`, `unit_sweep_iff_unimodular` — §1.
* `m_eq_one_of_adjacent`, `collinear_of_unit_sweep` — §2, the collinear branch.
* `bottom_conj123` — §3, conjuncts 1–3 in the field's shape.
-/

namespace Nivat.TowerHbase

open Nivat Nivat.LE2 Nivat.MaxEnv

/-! ## §1  The step size is the determinant -/

/-- The two-dimensional exchange identity, unconditional (`ring` after unfolding). -/
theorem det_dot_exchange (nJ vJ vJ1 w : ℤ × ℤ) :
    det vJ w * dot nJ vJ1 - det vJ vJ1 * dot nJ w = dot nJ vJ * det vJ1 w := by
  simp only [dot, det]
  ring

/-- `Primitive n` says exactly that `dot n ·` is onto `ℤ`; this produces the `1` witness. -/
theorem exists_dot_eq_one {n : ℤ × ℤ} (hn : Primitive n) : ∃ w : ℤ × ℤ, dot n w = 1 := by
  obtain ⟨u, v, huv⟩ := hn
  refine ⟨(u, v), ?_⟩
  simp only [dot]
  linear_combination huv

/-- **`dot nJ vJ1` divides `det vJ vJ1`.**  The direction that turns unimodularity of the pair
`(vJ, vJ1)` into the step size.  Uses `Primitive nJ` and `dot nJ vJ = 0`, nothing else. -/
theorem dot_dvd_det {nJ vJ : ℤ × ℤ} (hnJ_prim : Primitive nJ) (hperp : dot nJ vJ = 0)
    (vJ1 : ℤ × ℤ) : dot nJ vJ1 ∣ det vJ vJ1 := by
  obtain ⟨w, hw⟩ := exists_dot_eq_one hnJ_prim
  refine ⟨det vJ w, ?_⟩
  have h := det_dot_exchange nJ vJ vJ1 w
  rw [hperp, hw, zero_mul, mul_one] at h
  linarith [h]

/-- The converse divisibility, from `Primitive vJ`.  Together with `dot_dvd_det` this is
`|dot nJ vJ1| = |det vJ vJ1|`. -/
theorem det_dvd_dot {nJ vJ vJ1 : ℤ × ℤ} (hvJ_prim : Primitive vJ) (hperp : dot nJ vJ = 0) :
    det vJ vJ1 ∣ dot nJ vJ1 := by
  obtain ⟨u, v, huv⟩ := hvJ_prim
  refine ⟨dot nJ (-v, u), ?_⟩
  have hw : det vJ (-v, u) = 1 := by
    simp only [det]
    linear_combination huv
  have h := det_dot_exchange nJ vJ vJ1 (-v, u)
  rw [hperp, hw, zero_mul, one_mul] at h
  linarith [h]

/-- **The step size, from the adjacency of the two chain directions.**

`hadj` is the unimodularity `det vJ vJ1 = ±1`; deriving it is banned for this lane, so it is a
hypothesis.  Given it, `hsweep : dot nJ vJ1 < 0` (`ChainPartsFeed.lean:218`) pins the sign.

⚠ `Primitive vJ` and `Primitive vJ1` are **not** hypotheses: they are useless here, since
`RegionClaim411.lean:854` has all three primitive at step `-2`.  The work is done by
`Primitive nJ` together with `hadj`. -/
theorem unit_sweep_of_adjacent {nJ vJ vJ1 : ℤ × ℤ}
    (hnJ_prim : Primitive nJ) (hperp : dot nJ vJ = 0)
    (hadj : det vJ vJ1 = 1 ∨ det vJ vJ1 = -1)
    (hsweep : dot nJ vJ1 < 0) : dot nJ vJ1 = -1 := by
  have hdvd : dot nJ vJ1 ∣ det vJ vJ1 := dot_dvd_det hnJ_prim hperp vJ1
  have hone : dot nJ vJ1 ∣ (1 : ℤ) := by
    rcases hadj with h | h
    · rwa [h] at hdvd
    · rw [h] at hdvd
      exact (dvd_neg).mp hdvd
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hone) with h | h
  · omega
  · exact h

/-- **The step-size debt is exactly the adjacency debt.**  Under the chain's own data the two
statements are equivalent, so no route to `dot nJ vJ1 = -1` avoids the unimodularity of
`(v_{ℓ_J}, v_{ℓ_{J-1}})`. -/
theorem unit_sweep_iff_unimodular {nJ vJ vJ1 : ℤ × ℤ}
    (hnJ_prim : Primitive nJ) (hvJ_prim : Primitive vJ) (hperp : dot nJ vJ = 0)
    (hsweep : dot nJ vJ1 < 0) :
    dot nJ vJ1 = -1 ↔ (det vJ vJ1 = 1 ∨ det vJ vJ1 = -1) := by
  constructor
  · intro h
    have hdvd : det vJ vJ1 ∣ dot nJ vJ1 := det_dvd_dot hvJ_prim hperp
    rw [h] at hdvd
    exact Int.isUnit_iff.mp (isUnit_of_dvd_one ((dvd_neg).mp hdvd))
  · intro h
    exact unit_sweep_of_adjacent hnJ_prim hperp h hsweep

/-! ## §2  The collinear branch

lane-leafa-shell's `J = ι+1` configuration gives `vJ1 = m • vl` with `m > 0` (their
`tmp/wip/lane-leafa-shell-detvl.lean`, `shellSubStrip_free_of_nsmul`; recorded as
"lane-leafa-shell reports", §55 — **not** taken as a main-repo fact, which is why `hm` and
`hmpos` are hypotheses).

Two routes to `m = 1` are recorded.  `m_eq_one_of_adjacent` is the non-circular one; it does
not presuppose the step size.  `collinear_of_unit_sweep` is the "both sides pin each other"
reading, and it *does* presuppose the step size — it derives `-1` for `vl` from `-1` for `vJ1`,
it does not produce `-1`.
-/

/-- `det` is `ℤ`-linear in its second slot. -/
theorem hbase_det_zsmul (u v : ℤ × ℤ) (m : ℤ) : det u (m • v) = m * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- `dot` is `ℤ`-linear in its second slot. -/
theorem dot_zsmul_snd (n v : ℤ × ℤ) (m : ℤ) : dot n (m • v) = m * dot n v := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **Adjacency collapses the collinear branch's parameter, without assuming the step size.**
`det vJ vJ1 = m * det vJ vl`, so `m ∣ ±1`, so `m = 1` and `vJ1` *is* `vl`. -/
theorem m_eq_one_of_adjacent {vJ vJ1 vl : ℤ × ℤ} {m : ℤ}
    (hm : vJ1 = m • vl) (hmpos : 0 < m)
    (hadj : det vJ vJ1 = 1 ∨ det vJ vJ1 = -1) : m = 1 ∧ vJ1 = vl := by
  have hd : det vJ vJ1 = m * det vJ vl := by rw [hm, hbase_det_zsmul]
  have hdvd : m ∣ det vJ vJ1 := ⟨det vJ vl, hd⟩
  have hone : m ∣ (1 : ℤ) := by
    rcases hadj with h | h
    · rwa [h] at hdvd
    · rw [h] at hdvd
      exact (dvd_neg).mp hdvd
  have hm1 : m = 1 := by
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hone) with h | h
    · exact h
    · omega
  exact ⟨hm1, by rw [hm, hm1, one_smul]⟩

/-- **The step size pins both sides of the collinear branch at once.**  From
`m * dot nJ vl = -1` with `0 < m`.  ⚠ This consumes `dot nJ vJ1 = -1`; it does not produce it. -/
theorem collinear_of_unit_sweep {nJ vJ1 vl : ℤ × ℤ} {m : ℤ}
    (hm : vJ1 = m • vl) (hmpos : 0 < m) (hunit : dot nJ vJ1 = -1) :
    m = 1 ∧ vJ1 = vl ∧ dot nJ vl = -1 := by
  have hmul : m * dot nJ vl = -1 := by rw [← dot_zsmul_snd, ← hm]; exact hunit
  have hone : m ∣ (1 : ℤ) := (dvd_neg).mp ⟨dot nJ vl, hmul.symm⟩
  have hm1 : m = 1 := by
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hone) with h | h
    · exact h
    · omega
  refine ⟨hm1, by rw [hm, hm1, one_smul], ?_⟩
  rw [hm1, one_mul] at hmul
  exact hmul

/-! ## §3  `bottom`'s conjuncts 1–3 -/

/-- Iterate `rec_vJ` along `ℕ`. -/
theorem mem_of_natCast_smul {Ah : Set (ℤ × ℤ)} {vJ g₀ : ℤ × ℤ}
    (hrec : ∀ g ∈ Ah, g + vJ ∈ Ah) (hg₀ : g₀ ∈ Ah) :
    ∀ n : ℕ, g₀ + (n : ℤ) • vJ ∈ Ah := by
  intro n
  induction n with
  | zero => simpa using hg₀
  | succ n ih =>
      have hstep := hrec _ ih
      have he : g₀ + (n : ℤ) • vJ + vJ = g₀ + ((n + 1 : ℕ) : ℤ) • vJ := by
        push_cast; module
      rwa [he] at hstep

/-- `dot` expands along a `zsmul` shift. -/
theorem hbase_dot_add_zsmul (n g v : ℤ × ℤ) (k : ℤ) : dot n (g + k • v) = dot n g + k * dot n v := by
  simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **With a unit sweep, every level below `dot nJ g₀` is hit exactly, on the nose.**  This is
the only place the step size is used, and it is used for its *exactness*: from the **fixed** seed
`g₀` the reachable levels are the single progression `dot nJ g₀ - t · e`, `e := -dot nJ vJ1`, so
hitting `cJ - ε - 1` for every `ε` needs `e = 1`.

⚠ **Scope, corrected 2026-09-25.**  The previous version of this docstring said conjunct 1
(`ChainPartsFeed.lean:289`) "demands the level `cJ - ε - 1` for every `ε`, so the reachable levels
must form a progression of common difference 1".  **That inference is invalid**: conjunct 1 asks
for membership in `MaxEnv.reachSet Ah vJ1`, which is the **union over `g ∈ Ah`** of those
progressions, not one progression.  The seed-fixed converse is
`unit_sweep_of_forall_level` below; the union-level statement is **false**, see the ⛔ section at
the end of this file. -/
theorem exists_level_of_unit_sweep {nJ vJ1 g₀ : ℤ × ℤ} {cJ : ℤ} {ε : ℕ}
    (hd : dot nJ vJ1 = -1) (hge : cJ ≤ dot nJ g₀) :
    ∃ t : ℕ, dot nJ (g₀ + (t : ℤ) • vJ1) = cJ - (ε : ℤ) - 1 := by
  refine ⟨(dot nJ g₀ - cJ + (ε : ℤ) + 1).toNat, ?_⟩
  have hnn : (0 : ℤ) ≤ dot nJ g₀ - cJ + (ε : ℤ) + 1 := by
    have : (0 : ℤ) ≤ (ε : ℤ) := Int.natCast_nonneg ε
    omega
  have hc : (((dot nJ g₀ - cJ + (ε : ℤ) + 1).toNat : ℕ) : ℤ)
      = dot nJ g₀ - cJ + (ε : ℤ) + 1 := Int.toNat_of_nonneg hnn
  rw [hbase_dot_add_zsmul, hd, hc]
  ring

/-- **The seed form**, with the sweep length `t` and the layer index `ε` both handed in.

This is the whole content of conjuncts 1–3: given *any* seed `a + wS` whose `t`-th sweep lands on
the level `cJ - ε - 1`, the three conjuncts follow at `L = 0` with no arithmetic left.  Isolating
it makes visible that the step size enters `bottom` in exactly one place — whether such a `t`
exists for the given `ε` — and nowhere else. -/
theorem bottom_conj123_of_seed {Ah : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {nJ vJ vJ1 a wS : ℤ × ℤ} {cJ : ℤ} {ε t : ℕ}
    (ha : a ∈ S) (htile : ∀ b ∈ S, b + wS ∈ Ah)
    (hrec : ∀ g ∈ Ah, g + vJ ∈ Ah)
    (hperp : dot nJ vJ = 0)
    (hlev : dot nJ ((a + wS) + (t : ℤ) • vJ1) = cJ - (ε : ℤ) - 1) :
    ∃ (z₀ : ℤ × ℤ) (L : ℤ), dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet Ah vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k → z₀ + k • vJ + (b - a) ∈ MaxEnv.reachSet Ah vJ1) ∧
      (∀ k : ℤ, L ≤ k → dot nJ (z₀ + k • vJ) = cJ - (ε : ℤ) - 1) := by
  have hg₀ : a + wS ∈ Ah := htile a ha
  refine ⟨(a + wS) + (t : ℤ) • vJ1, 0, hlev, ?_, ?_, ?_⟩
  · intro k hk
    refine ⟨(a + wS) + k • vJ, ?_, t, ?_⟩
    · have hk' : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk
      have := mem_of_natCast_smul hrec hg₀ k.toNat
      rwa [hk'] at this
    · module
  · intro b hb k hk
    refine ⟨(b + wS) + k • vJ, ?_, t, ?_⟩
    · have hk' : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk
      have := mem_of_natCast_smul hrec (htile b hb) k.toNat
      rwa [hk'] at this
    · module
  · intro k _
    rw [hbase_dot_add_zsmul, hperp, mul_zero, add_zero]
    exact hlev

/-- **`bottom`'s conjuncts 1, 2 and 3** (`ChainPartsFeed.lean:289`, `:290`, `:291-292`), for
every `ε`, in the field's shape — instantiate `Ah := ⋃ i, hatOf A kk vl i` and `a := F.a`.

The witness is `z₀ := (a + wS) + t • vJ1` with `L := 0`, `t` from `exists_level_of_unit_sweep`.

⭐ **Why conjunct 3 is nearly free, and what `F.a` is doing there.**
`z₀ + k • vJ + (b - a) = ((b + wS) + k • vJ) + t • vJ1`: the `a` cancels, so the *same* `t`
serves, and the seed merely moves from `a + wS` to `b + wS`, which `htile` supplies.  Conjunct
3 is therefore not an extra integer condition — it is conjunct 2 re-seeded.

The fourth component of the conclusion is **not** conjunct 4; it is the ray-level fact
`dot nJ (z₀ + k • vJ) = cJ - ε - 1`, free from `hperp`, and it is exported because conjunct 4
(`ChainPartsFeed.lean:293-294`) is stated against exactly that ray.  Conjunct 4 itself is
lane-hole3-nlmax's and is not attempted here.

⚠ Conjuncts 1–3 use **neither** `dot nJ vJ = 0` **nor** any primitivity; `hperp` enters only
for the exported ray-level fact.  `L = 0` is forced by `rec_vJ` being a forward recurrence. -/
theorem bottom_conj123 {Ah : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {nJ vJ vJ1 a wS : ℤ × ℤ} {cJ : ℤ}
    (ha : a ∈ S) (htile : ∀ b ∈ S, b + wS ∈ Ah)
    (hhp : ∀ z ∈ Ah, cJ ≤ dot nJ z)
    (hrec : ∀ g ∈ Ah, g + vJ ∈ Ah)
    (hperp : dot nJ vJ = 0) (hd : dot nJ vJ1 = -1) :
    ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ), dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet Ah vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k → z₀ + k • vJ + (b - a) ∈ MaxEnv.reachSet Ah vJ1) ∧
      (∀ k : ℤ, L ≤ k → dot nJ (z₀ + k • vJ) = cJ - (ε : ℤ) - 1) := by
  intro ε
  obtain ⟨t, hlev⟩ := exists_level_of_unit_sweep (ε := ε) hd (hhp _ (htile a ha))
  exact bottom_conj123_of_seed ha htile hrec hperp hlev

/-! ### ⭐ Where `dot nJ vJ1 = -1` actually came from: the `∀ ε`, not the source

`scratch/b3_colle2.txt` never asks the sweep step to be a unit.  Measured:

* `:440` (and its `(ii)` twin `:458`, and the finite-stage `:518`) define the shell with the
  sweep parameter **free**: `Â_∞^{(ε)} := {g + t·v⃗_{ℓ_{J-1}} : g ∈ Â_∞, t ∈ ℤ₊, …}`.  `t` ranges
  over all of `ℤ₊`; there is no sentence constraining one step of `v⃗_{ℓ_{J-1}}` against `ℓ_J`.
* `:442` is what makes `Â^{(ε+1)} ∖ Â^{(ε)}` a *single* line: `0 = d_0 < d_1 < ⋯` is the
  increasing enumeration of the distances **actually attained** on `H(ℓ_J)`.  So consecutive
  layer indices are consecutive *attained* distances — which `MaxEnv.shell`'s `c - ε` encodes
  faithfully because `Primitive nJ` makes `dot nJ` surjective onto `ℤ`.  That is a statement
  about the layer index, **not** about the step size.
* `:351` does pin `v⃗_ℓ` to be "the non-zero vector parallel to `ℓ` of minimum norm", i.e.
  `Primitive vJ1` is in the source.  It does not give `-1`: `RegionClaim411.lean:854`/`:859` and
  `CyclicOrderAdjRefute.adj_premises_hold` (`CyclicOrderAdjRefute.lean:202`) both exhibit all
  three vectors primitive with step `-2`.
* `:432`/`:436` — the *consuming* statement (3.1) — quantifies the layer index as
  **`∃ ε ∈ ℤ₊`**, not `∀ ε`.  `:438`'s "for each `ε ∈ ℤ₊`" governs only the *definition* of
  `Â^{(ε)}`, and `:516`'s `∀ ε` is the contradiction hypothesis, not an obligation.

`ChainDataGeomParts.bottom` (`ChainPartsFeed.lean:288`) opens with `∀ ε : ℕ`.  **That is our
added quantifier**, and it is the reason `-1` entered *this file's* route: our witness sweeps from
**one** seed `a + wS`, and with step `-(s+1)` a single seed reaches only the levels
`dot nJ (a + wS) - t·(s + 1)`, one arithmetic progression, so asking that seed for a point on
every level forces `s = 0` (`unit_sweep_of_forall_level`, at the end of this file, is that
implication with the single seed written into the signature).  `exists_eps_bottom_conj123` below
discharges conjuncts 1–3 in the `∃ ε` shape for **any** `hsweep : dot nJ vJ1 < 0`, with no `hadj`,
no `Primitive` and no unit step: take `t := r + 1` where `r := dot nJ (a + wS) - cJ ≥ 0` (from
`hhp`), which lands on `ε = (r + 1) · s`.

⛔ **The same implication at the field's level is false, corrected 2026-09-25.**  An earlier
version of this paragraph said the `∀ ε` "is the sole reason `-1` was needed", which reads as a
claim about conjunct 1 rather than about our seed.  Conjunct 1 asks for
`MaxEnv.reachSet Ah vJ1`, a **union** of progressions over `g ∈ Ah`; distinct `g` may cover
distinct residues mod `e`, and then `∀ ε` costs nothing.  Kernel witness:
`Nivat.ShellConvex.cgc` (`ShellConvex.lean:586`) is a field-complete `ChainDataGeom` whose
`bottom` is proved and whose step is `-2` (`cgc_dot_nJ_vJ1`, `ShellConvex.lean:873`) — restated as
`Nivat.CyclicOrderStepT.unit_sweep_not_of_chainDataGeom` (`CyclicOrderStepT.lean:84`).  ⚠ Scope,
per lane-tower-hlev: `cgc`'s window is a single point and its `Env` is trivially true, so what it
refutes is the abstract signature.

⟹ The correct statement of what `∀ ε` buys is **not** about the step but about the residues of
`Ah`'s heights mod `e`: `not_bottom_conj1_of_common_residue` (`CyclicOrderStepT.lean:113`) and
`step_eq_one_of_bottom_of_common_residue` (`:142`), whose explicit premise is
`hres : ∀ g ∈ A, e ∣ (dot nJ g - cJ)`.
⛔ **Not** "our single seed is the extreme case of `hres`" — that phrasing stood here until
2026-09-25 and is false, see the negative-control section below and
`CyclicOrderStepT.dvd_height_iff_of_seed_level` (lane-env-refute's, by name: line numbers on that
file are deliberately not carried here).
⚠ Those two are lane-env-refute's declarations; EXIT/axioms not re-run here (§55).

⚠ This does still **not** say the `∀ ε` is wrong — `ChainDataGeom`'s consumers may genuinely need
it, and that is not decided here.  It says the debt `hadj` carries is `hres`-shaped: a placement
condition on `Â_∞`, chargeable neither to the geometry alone nor to the layer quantifier alone. -/

/-- **Conjuncts 1–3 in the source's `∃ ε` shape, for an arbitrary sweep step.**  No `hadj`, no
`Primitive`, no `dot nJ vJ1 = -1` — only `hsweep : dot nJ vJ1 < 0` (the field `hsweep`,
`ChainPartsFeed.lean:218`) and `hhp` (`ChainPartsFeed.lean:220`).

Paper: the layer index of (3.1) is `∃ ε ∈ ℤ₊` (`b3_colle2.txt:432`), and the sweep parameter of
`:440` is free in `ℤ₊`; this theorem is those two quantifiers taken at face value. -/
theorem exists_eps_bottom_conj123 {Ah : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {nJ vJ vJ1 a wS : ℤ × ℤ} {cJ : ℤ}
    (ha : a ∈ S) (htile : ∀ b ∈ S, b + wS ∈ Ah)
    (hhp : ∀ z ∈ Ah, cJ ≤ dot nJ z)
    (hrec : ∀ g ∈ Ah, g + vJ ∈ Ah)
    (hperp : dot nJ vJ = 0) (hsweep : dot nJ vJ1 < 0) :
    ∃ (ε : ℕ) (z₀ : ℤ × ℤ) (L : ℤ), dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet Ah vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k → z₀ + k • vJ + (b - a) ∈ MaxEnv.reachSet Ah vJ1) ∧
      (∀ k : ℤ, L ≤ k → dot nJ (z₀ + k • vJ) = cJ - (ε : ℤ) - 1) := by
  have hge : cJ ≤ dot nJ (a + wS) := hhp _ (htile a ha)
  obtain ⟨r, hr⟩ : ∃ r : ℕ, dot nJ (a + wS) = cJ + (r : ℤ) :=
    ⟨(dot nJ (a + wS) - cJ).toNat, by rw [Int.toNat_of_nonneg (by omega)]; ring⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ, dot nJ vJ1 = -(s : ℤ) - 1 :=
    ⟨(-dot nJ vJ1 - 1).toNat, by rw [Int.toNat_of_nonneg (by omega)]; ring⟩
  refine ⟨(r + 1) * s, bottom_conj123_of_seed (t := r + 1) ha htile hrec hperp ?_⟩
  rw [hbase_dot_add_zsmul, hr, hs]
  push_cast
  ring

/-- The same three conjuncts with the step size replaced by its real source, the adjacency.
This is the form a `ChainDataGeomParts` producer instantiates: every hypothesis except `hadj`
and `htile` is a field. -/
theorem bottom_conj123_of_adjacent {Ah : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {nJ vJ vJ1 a wS : ℤ × ℤ} {cJ : ℤ}
    (ha : a ∈ S) (htile : ∀ b ∈ S, b + wS ∈ Ah)
    (hhp : ∀ z ∈ Ah, cJ ≤ dot nJ z)
    (hrec : ∀ g ∈ Ah, g + vJ ∈ Ah)
    (hnJ_prim : Primitive nJ) (hperp : dot nJ vJ = 0)
    (hadj : det vJ vJ1 = 1 ∨ det vJ vJ1 = -1) (hsweep : dot nJ vJ1 < 0) :
    ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ), dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet Ah vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k → z₀ + k • vJ + (b - a) ∈ MaxEnv.reachSet Ah vJ1) ∧
      (∀ k : ℤ, L ≤ k → dot nJ (z₀ + k • vJ) = cJ - (ε : ℤ) - 1) :=
  bottom_conj123 ha htile hhp hrec hperp
    (unit_sweep_of_adjacent hnJ_prim hperp hadj hsweep)

/-! ## The converse: `bottom` has no witness other than the reach-minimal one

lane-hole3-nlmax's objection to `bottom_conj123`'s witness is correct, and this section makes
it a kernel fact rather than an argument.  `bottom_conj123` puts `z₀ := (F.a + wS) + t • vJ1`
on the level line `⟪nJ,·⟫ = cJ - ε - 1` and nothing more; conjunct 4
(`ChainPartsFeed.lean:293-294`) additionally demands that **every** reachable point of that
line be `z₀ + k • vJ` with `L ≤ k`, i.e. that `z₀ + L • vJ` be the `vJ`-least such point.

`reachMin_of_bottom` below shows the demand is not an artefact of how one reads the field:
from conjuncts 1–4 at *any* pair `(z₀, L)` one recovers, at the single point `w₀ := z₀ + L • vJ`,
exactly the four inputs that `Nivat.BottomReachMin.bottom_of_reachMin` (`BottomReachMin.lean:151`)
consumes — level, membership, reach-minimality (`hline0`), and the whole window slice
`∀ b ∈ S, w₀ + (b - F.a) ∈ reachSet`.  Two consequences:

* ⛔ **Raising `L` is not a repair.**  Whatever `L` a producer picks, conjunct 4 forces
  `z₀ + L • vJ` to be *the* reach-minimum, so the window slice is owed at the reach-minimum and
  nowhere else.  `bottom_conj123`'s witness satisfies conjuncts 1–3 at `L = 0` but sits at
  `w₀ + m • vJ` for an unknown `m ≥ 0`, and only the `m = 0` case is a `bottom` witness.
* ⭐ **`bottom_of_reachMin` is lossless.**  Together with it this is an equivalence: `bottom`
  holds iff the reach-minimum of the level line exists and carries the window slice.  So no
  cheaper witness can be searched for — the remaining content of `bottom` is entirely the
  window slice at the reach-minimum, which `BottomReachMin.lean:52-96` documents as `hhigh`
  and reports **false at that abstraction level** (two kernel witnesses in `tmp/wip/`,
  `lane-cd-hhigh-refute.lean` and `lane-cd-hhigh-refute2.lean`; ⚠ not re-verified here, §55).

⚠ This section proves nothing about whether a real tower has such a point; it only pins the
shape of any witness. -/

/-- **Every `bottom` witness is the reach-minimal one.**  Conjuncts 1–4 at `(z₀, L)` yield, at
`w₀ := z₀ + L • vJ`, the four hypotheses of `BottomReachMin.bottom_of_reachMin`
(`BottomReachMin.lean:151`): `hdz`, `hz₀`, `hline0`, and the `L = 0` window slice.

The reach-minimality step is the only one with content: a reachable point `z` at level
`cJ - ε - 1` lies in `shell … (ε + 1)` by `MaxEnv.mem_shell_succ_iff` (`ShellLine.lean:54`), and
its `shell … ε` alternative is impossible because that shell's bound is `cJ - ε ≤ ⟪nJ,z⟫`
(`MaxEnv.shell_eq_reach_inter`, `ShellLine.lean:43`) while `z` sits one level below it.

`hperp` (`FaceBlock.dot_nJ_vJ`, `ANormal.lean:616`) is used only to move the level from `z₀` to
`w₀`. -/
theorem reachMin_of_bottom {T : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {nJ vJ vJ1 a z₀ : ℤ × ℤ} {cJ : ℤ} {ε : ℕ} {L : ℤ}
    (hperp : dot nJ vJ = 0)
    (h1 : dot nJ z₀ = cJ - (ε : ℤ) - 1)
    (h2 : ∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet T vJ1)
    (h3 : ∀ b ∈ S, ∀ k : ℤ, L ≤ k → z₀ + k • vJ + (b - a) ∈ MaxEnv.reachSet T vJ1)
    (h4 : ∀ z ∈ MaxEnv.shell T vJ1 nJ cJ (ε + 1),
      z ∈ MaxEnv.shell T vJ1 nJ cJ ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ) :
    ∃ w₀ : ℤ × ℤ, dot nJ w₀ = cJ - (ε : ℤ) - 1 ∧ w₀ ∈ MaxEnv.reachSet T vJ1 ∧
      (∀ z ∈ MaxEnv.reachSet T vJ1, dot nJ z = cJ - (ε : ℤ) - 1 →
        ∃ k : ℤ, 0 ≤ k ∧ z = w₀ + k • vJ) ∧
      (∀ b ∈ S, w₀ + (b - a) ∈ MaxEnv.reachSet T vJ1) := by
  refine ⟨z₀ + L • vJ, ?_, h2 L le_rfl, ?_, fun b hb => h3 b hb L le_rfl⟩
  · rw [hbase_dot_add_zsmul, hperp, mul_zero, add_zero]
    exact h1
  · intro z hz hlev
    have hmem : z ∈ MaxEnv.shell T vJ1 nJ cJ (ε + 1) :=
      MaxEnv.mem_shell_succ_iff.mpr (Or.inr ⟨hz, hlev⟩)
    rcases h4 z hmem with hsh | ⟨k, hk, rfl⟩
    · rw [MaxEnv.shell_eq_reach_inter] at hsh
      have hge := hsh.2
      simp only [Set.mem_ofPred_eq] at hge
      omega
    · exact ⟨k - L, by omega, by module⟩

/-! ### ⭐ `htile` 的真正产者形状是 `HsuppContain.hcont`，不是 `fillCover`（2026-09-25 订正）

**我上一轮建议「把种子前提改成从 `fillCover` 走」，这条建议是错的，方向反了。**
`fillCover`（`ChainPartsFeed.lean:271`）的结论是
`shellInter … ⊆ {z | Colle37.GenClosure S D z}`，而 `GenClosure` 是**闭包算子**：
唯一的入口构造子是 `base : z ∈ D → GenClosure S D z`（`GenClosureDef.lean:27`）。
所以 `fillCover` 只能把「已在 `shellInter` 里」换成「在 `GenClosure` 里」，
**给不出任何 `z ∈ Ah` 形的成员关系**。集成者据我那条建议批了改签名，此处撤回。

**真正同形的产者已经在树里，0 sorry：**`Nivat.HsuppContain.hcont`（`HsuppContain.lean:413`）

    ∀ b ∈ ↑d.toDecompData.Sphi, V + (b - a) ∈ B

取 `wS := V - a` 就有 `b + wS = V + (b - a)`（`hcont` 自己的证明末尾就在做这步换算），
所以 **`htile` 与 `hcont` 的结论逐字相同**，`htile` 不是新债。下面 `htile_iff_window`
把这件事钉成内核事实。

**⚠ 但 `hcont` 不是最便宜的路，`htile` 另有一条不吃包络性的产者。**
`exists_tile_of_parts_binders`（`TowerHlevTile.lean`，lane-tower-hlev 的文件，按名引不带行号）
直接给出 `∃ wS, ∀ b ∈ S, b + wS ∈ ⋃ i, hatOf A kk vl i`，
前提逐条是 `ChainDataGeomParts` 的字段（`maxA`/`hfin`/`AhatMono`/`ahat_nonempty`/`hhp`/
`hswept`/`rec_p`/`dot_nJ_p`/`hsweep`）**外加一条 `hindep : det p vJ1 ≠ 0`**。
机制与包络性无关：`Â_∞` 在 `p` 与 `Q•p + P•vJ1` 两个线性无关方向上封闭
（`exists_tile_of_swept`，同文件），两个独立平移就逼出任意有限集的一个平移。
同文件 `bottom_conj123_of_tile` 已经把它接到我的 `bottom_conj123_of_adjacent` 上。

⛔ **路径沿革（两次订正，都写下来）**：
1. 上上一版把那三条写成主仓 `TowerHlevTile.lean` 而主仓当时**没有**该文件
   （`find . -name "TowerHlevTile*"` 零命中），实体在 `tmp/wip/hlev-tile.lean`。
2. **2026-09-25 20:21 hlev 已把它落进主仓** `Nivat/External/Colle/TowerHlevTile.lean`
   （实测存在，且 `grep -l '^import Nivat.External.Colle.TowerHbaseUnitSweep'` 命中它 ⟹ 它引本文件）。
   ✅ **2026-09-25 集成者第六次 build（窗口 20:37:45–20:38:16）覆盖了它**：
   `BUILD_RC=0`、`sorryAx` 计数 0、census `lean_files=420 missing_oleans=0`，
   且 `.lake/build/lib/lean/Nivat/External/Colle/TowerHlevTile.olean` **存在**（本 lane 实测
   20:38:08，`Nivat/All.lean` 里有该 import）⟹ 硬规矩 1 的「贡献为零」不再适用。
   ⚠ 收据本身是集成者所报，我复核的只是 olean 与 `All.lean` 这两项（§55）。
⚠ 行号一律不带（第 230 轮同一文件的行号在三人之间烂了 4 次）；按标识符名查 `declscan.py`。

⟹ 排序：`htile` 的**候选**产者是 hlev 那条（不吃 `DecompDataZ`、不吃包络性，残债 `hindep`）；
`hcont` 是**第二条独立的路**，贵一些（要 `DecompDataZ` ＋ `hEeq`/`henv`），但它在 build 里。
登记下来是因为它与 `hwin` 共用同一个输入，见下。

⚠ `bottom_conj123_of_tile` 仍带 `hadj : det vJ vJ1 = ±1`（经 `bottom_conj123_of_adjacent`），
而 `hadj` 在链上有反例 ⟹ 那条**不是**合取 1–3 的终点。去掉 `hadj` 的版本是
`bottom_conj123_of_rec_p_of_tile`（`TowerHbaseRecP.lean`，本 lane），残余换成
`IsCoprime (dot nJ p) (dot nJ vJ1)`。
⚠ hlev 那条的 EXIT / 公理我未复核，按 §55 记为「lane-hlev 所报，我只核了签名」。

⟹ `hwin`（`BottomRoom.window_of_shell`（`BottomRoom.lean`，按名查））与它的输入
`shellEnv`（`ChainPartsFeed.lean`，按标识符名查）仍然是一个洞：`hcont` 从 `hEeq`/`henv` 出发，
而那两条就是 `shellEnv`，原文只在 `:516`/`:520` 断言、从不证明。
**但 `htile` 已经不在这个洞里了** —— 它走的是 hlev 的平移路线。

### ⛔ 负控：单位模与朝向是两个独立自由度（已内核化，lane-leafa-shell 报）

将来即使 `det vJ vJ1 = ±1` 真有了产者，它**不会**顺带解决 `vJ` 的朝向：
把 `vJ` 换成 `-vJ`，`det vJ vJ1` 翻号而 `±1` 仍成立，但 `vJ = k • dir J` 的 `k` 翻号。
⟹ 单位模收的是 `m`（模长），朝向收的是 `k` 的符号，两边都得单独有产者。

这条现在不再是散记，而是一条定理：`fork_refutation_needs_m_pos`
（`LeafAShellLsideFork.lean`，lane-leafa-shell），结论是
`m ≠ 0 ∧ (0 < m → kJ < 0) ∧ (m < 0 → 0 < kJ)` —— **模长比特与朝向比特在同一条
恒等式里是两个独立的量**，且 `m ≠ 0` 是免费的（不需要任何朝向输入）。
相关的两个反向洞在 `LeafAShellAttain.lean` 的 `k_nonneg_of_hattain` 与
`k_neg_of_det_p_vJ_pos`，两者要求相反的符号（`not_hattain_of_vjsign_choice`）。
⚠ 以上 EXIT/公理均为 lane-leafa-shell 所报，我未复核（§55）；此处只作负控登记，
不作为任何证明的输入。第 179 轮红线仍然禁止两个方向搬动朝向判据。
⚠ 跳 lane 引用不带行号（§124）：只写文件名＋标识符名。
-/

/-- **`htile` 与 `hcont` 的结论逐字相同**，在 `wS = V - a` 下。

这条不是引理而是登记：它说明本文件的种子前提 `∀ b ∈ S, b + wS ∈ Ah` 不需要新产者，
`HsuppContain.hcont`（`HsuppContain.lean`，按名查）的结论换个拼写就是它。 -/
theorem htile_iff_window {Ah : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)} {a V : ℤ × ℤ} :
    (∀ b ∈ S, b + (V - a) ∈ Ah) ↔ (∀ b ∈ S, V + (b - a) ∈ Ah) := by
  constructor <;> intro h b hb
  · have hm := h b hb
    rwa [show b + (V - a) = V + (b - a) by abel] at hm
  · have hm := h b hb
    rwa [show V + (b - a) = b + (V - a) by abel] at hm

/-- **`bottom` 合取 1–3，以 `hcont` 的拼写吃种子前提。**

与 `bottom_conj123_of_seed` 同一条，只把 `htile` 换成 `HsuppContain.hcont`
（`HsuppContain.lean`，按名查）逐字的结论形，锚点 `V` 显式。这样调用点不需要先构造 `wS`。 -/
theorem bottom_conj123_of_window {Ah : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)}
    {nJ vJ vJ1 a V : ℤ × ℤ} {cJ : ℤ} {ε t : ℕ}
    (ha : a ∈ S) (hwin : ∀ b ∈ S, V + (b - a) ∈ Ah)
    (hrec : ∀ g ∈ Ah, g + vJ ∈ Ah)
    (hperp : dot nJ vJ = 0)
    (hlev : dot nJ (V + (t : ℤ) • vJ1) = cJ - (ε : ℤ) - 1) :
    ∃ (z₀ : ℤ × ℤ) (L : ℤ), dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet Ah vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k → z₀ + k • vJ + (b - a) ∈ MaxEnv.reachSet Ah vJ1) ∧
      (∀ k : ℤ, L ≤ k → dot nJ (z₀ + k • vJ) = cJ - (ε : ℤ) - 1) := by
  have htile : ∀ b ∈ S, b + (V - a) ∈ Ah := htile_iff_window.mpr hwin
  have hVa : a + (V - a) = V := by abel
  refine bottom_conj123_of_seed (wS := V - a) (t := t) ha htile hrec hperp ?_
  rwa [hVa]

/-! ### ⛔ 负控：单位步长是**种子形**的定理，不是 `bottom` 的定理（2026-09-25）

集成者第 230 轮的裁决要求把本文件那条「`∀ ε` 迫出单位步长」的机制定性成两者之一：
(a) 它在种子构造的额外前提下成立、那条前提必须显式进签名；(b) 它有洞。

**答案是 (a)，而且前提比预想的窄**：只要层号 `ε = 0` 与 `ε = 1` 两档由**同一个**点 `g₀`
的 `vJ1`-射线兑现，步长就是 `-1`。下面这条把「同一个 `g₀`」写进签名。

⛔ 把 `g₀` 换成 `∀ ε` 各自可选的点（也就是 `MaxEnv.reachSet Ah vJ1`，`bottom` 合取 1 的
真实形状）之后结论为**假**——见本文件上方 §「Where `dot nJ vJ1 = -1` actually came from」
里的 `cgc` 见证。两者不矛盾：`reachSet` 是对 `g ∈ Ah` 取并，不同 `g` 可以覆盖不同剩余类。 -/

/-- **单位步长的逆向：两档层号 + 同一个种子 ⟹ `dot nJ vJ1 = -1`。**

`exists_level_of_unit_sweep` 的逆命题，前提逐字是本文件的构造实际用到的那条：`ε = 0` 与
`ε = 1` 两个层号都由**固定**的 `g₀` 扫到。证法不需要剩余类：两式相减直接得
`(t₁ - t₀) · dot nJ vJ1 = -1`，于是 `dot nJ vJ1 ∣ 1`。

⚠ 只用到 `ε ∈ {0, 1}`，`∀ ε` 是多余的；⛔ 而把 `g₀` 放成每个 `ε` 各自的点就为假
（`cgc`，`ShellConvex.lean:586`）。原文对应物：**没有**——`b3_colle2.txt` 的 sweep 参数在
`:440`/`:458`/`:518` 处自由，所以这条记的是我们这条路线的代价，不是原文的一步。

⛔ **本条与 lane-env-refute 的 `step_eq_one_of_bottom_of_common_residue`（`CyclicOrderStepT.lean`，
按名引，不带行号）互不蕴含；此处曾写「本条是它的 `hres` 退化到单点的情形」，那句为假，
2026-09-25 订正。** 理由是内核的：在本条的 `hlev0` 之下，`dot nJ g₀ - cJ = t₀ · dot nJ vJ1 - 1`，
⟹ 种子高度模 `e := -dot nJ vJ1` 的余数恒为 `-1`，于是「`hres` 落在 `g₀` 上」⟺ `e ∣ 1` ⟺ 结论本身。
把那条实例化到 `A = {g₀}` 因此是**循环**，不是特化——见
`CyclicOrderStepT.dvd_height_iff_of_seed_level` / `step_eq_one_of_res_of_seed_level`
（lane-env-refute 落的，EXIT/公理本处未复跑，§55）。

真正的分工：本条吃**两档**层号（`ε ∈ {0,1}`）、种子**固定**、不要同余；那条吃**一档**层号、
种子在 `reachSet` 里任取、要 `hres`。两条各是 `e ∣ 1` 的一种取法。 -/
theorem unit_sweep_of_forall_level {nJ vJ1 g₀ : ℤ × ℤ} {cJ : ℤ}
    (hsweep : dot nJ vJ1 < 0)
    (hlev0 : ∃ t : ℕ, dot nJ (g₀ + (t : ℤ) • vJ1) = cJ - ((0 : ℕ) : ℤ) - 1)
    (hlev1 : ∃ t : ℕ, dot nJ (g₀ + (t : ℤ) • vJ1) = cJ - ((1 : ℕ) : ℤ) - 1) :
    dot nJ vJ1 = -1 := by
  obtain ⟨t₀, h₀⟩ := hlev0
  obtain ⟨t₁, h₁⟩ := hlev1
  rw [hbase_dot_add_zsmul] at h₀ h₁
  push_cast at h₀ h₁
  have hdvd : dot nJ vJ1 ∣ (1 : ℤ) := ⟨(t₀ : ℤ) - (t₁ : ℤ), by linarith⟩
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h | h
  · omega
  · exact h

end Nivat.TowerHbase

#print axioms Nivat.TowerHbase.det_dot_exchange
#print axioms Nivat.TowerHbase.exists_dot_eq_one
#print axioms Nivat.TowerHbase.dot_dvd_det
#print axioms Nivat.TowerHbase.det_dvd_dot
#print axioms Nivat.TowerHbase.unit_sweep_of_adjacent
#print axioms Nivat.TowerHbase.unit_sweep_iff_unimodular
#print axioms Nivat.TowerHbase.hbase_det_zsmul
#print axioms Nivat.TowerHbase.dot_zsmul_snd
#print axioms Nivat.TowerHbase.m_eq_one_of_adjacent
#print axioms Nivat.TowerHbase.collinear_of_unit_sweep
#print axioms Nivat.TowerHbase.mem_of_natCast_smul
#print axioms Nivat.TowerHbase.hbase_dot_add_zsmul
#print axioms Nivat.TowerHbase.exists_level_of_unit_sweep
#print axioms Nivat.TowerHbase.bottom_conj123_of_seed
#print axioms Nivat.TowerHbase.exists_eps_bottom_conj123
#print axioms Nivat.TowerHbase.bottom_conj123
#print axioms Nivat.TowerHbase.bottom_conj123_of_adjacent
#print axioms Nivat.TowerHbase.reachMin_of_bottom
#print axioms Nivat.TowerHbase.htile_iff_window
#print axioms Nivat.TowerHbase.bottom_conj123_of_window
#print axioms Nivat.TowerHbase.unit_sweep_of_forall_level
