/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.SweepLines
import Nivat.External.Colle.ConeRegion
import Nivat.External.Colle.ApexUnique
import Nivat.External.Colle.LineIndex

set_option autoImplicit false

/-!
# `StrictWindow` — the strict-argmax window, and `hwinL` from it

**原文：b3_colle2.txt:792-804.**

`SweepLines.lean:214-232` (§5, Goal 2b) establishes that line-indexing **alone** does not escape
`L1SweepBridge.not_hwin_of_row_zero_levelConst` (`L1SweepBridge.lean:749`): that refutation uses
only `i = 0`, where the line-indexed and the lexicographic right-hand sides both collapse to `D`.
The diagnosis recorded there is that the defect is the choice of `a` — argmin where the paper
takes the **outward extreme** point — and `SweepLines.translate_minus_apex_subset_of_argmax`
(`:252`) is the non-strict half of the fix.

This file supplies the strictness upgrade and the level-indexed consequence.

## The mechanism, in one line

With `a` the **strict** maximiser of `⟪m,·⟫` over `S`, every other generator sits at least one
level below it, so translating `S` to put `a` at `w` drops the whole punctured set at least one
level below `w`:

    ⟪m, z + (w − a)⟫ = ⟪m,z⟫ + ⟪m,w⟫ − ⟪m,a⟫ ≤ ⟪m,w⟫ − 1 .

Indexing the lines by level, `lines i := {z | ⟪m,z⟫ = c + 1 + i}` and `D := {z | ⟪m,z⟫ ≤ c}`, a
point of line `i` therefore throws its window to level `≤ c + i`, and every integer `≤ c + i` is
either `≤ c` — that is, in `D` — or equal to `c + 1 + i'` for exactly one `i' < i`.

**At `i = 0` the union term is empty and the conclusion is exactly `∈ D`**, which is where the
line-indexed form failed before: it is `hstrict` that discharges it here, not the indexing.

## Quantifier correspondence with the source

- `m` — the normal of the sweep lines.  The induction of `:792-804` is **transverse**
  (`l₁ := ℓ_B^{(-)}`, `l₂ := l₁^{(-)}`, …), so `m` is the normal with `⟪m,v⃗_ℓ⟫ = 0`, **not**
  `expNormal u' vl` (which satisfies `⟪·,v⃗_ℓ⟫ = 1` and is the along-line coordinate).  That
  mix-up is retracted at `SweepLines.lean:272-278`; it is not repeated here.
  ⚠ Transversality is **not needed by §1–§3** — that arithmetic is pure linearity.  It is what
  makes the remaining hypothesis `hD` satisfiable, since `{z | ⟪m,z⟫ ≤ c}` is invariant under
  the period `c_per • v⃗_ℓ` exactly when `⟪m,v⃗_ℓ⟫ = 0`.  §4 is the one place it is consumed as a
  hypothesis (`hperp`), and there it is what makes the `t = 0` gap unavoidable.
- `hstrict` ↔ `:792`, "Lemma 2.6 implies that `𝒮_{φ_ι}` does not have any edge parallel to `-ℓ`
  or `ℓ`" — no edge on the `m`-extreme face means the maximiser is unique, i.e. strict.
  **It is a hypothesis here and is not discharged**; producing it is Wbox's
  `NoEdgePlacement.unique_argmax_of_no_edge_parallel`.  §4 records what Figure 10's cone
  condition alone does and does not buy towards it.
- `lines i` ↔ `A_i = 𝓡_{ι-1} ∩ l_i` (`:798-804`), `D` ↔ `H_B(ℓ)` (`:777`).
- `i : ℕ` ↔ "proceeding this way, we get by induction" (`:804`).

## What comes out

`hbase_at_of_strict_argmax` composes the above with `SweepLines.hbase_at_of_sweep_lines`
(`:177`) and reduces `hbase` at index `k` to the **single** remaining hypothesis `hD`:
periodicity of `T^e ξ` on the half plane `{z | ⟪m,z⟫ ≤ c}`.  Both other binders of that engine
are free in this instantiation — `hwinL` from `hstrict`, and `hKL` because the seed together with
the level lines exhausts `ℤ²` (`mem_seed_union_lines`), so no property of `chainFull` is needed.
-/

namespace Nivat.StrictWindow

open Nivat

/-! ## §1. The window drop -/

/-- Translating `z` by `w - a` is linear on levels. -/
private theorem dot_translate_eq (m z w a : ℤ × ℤ) :
    Nivat.LE2.dot m (z + (w - a))
      = Nivat.LE2.dot m z + Nivat.LE2.dot m w - Nivat.LE2.dot m a := by
  simp only [Nivat.LE2.dot, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  ring

/-- **The strict drop.**  A strict maximiser puts every translated generator at least one level
below `w`.  This is the whole content of the strictness upgrade; everything else is bookkeeping.

原文：b3_colle2.txt:792 — the unique extreme vertex of `𝒮_{φ_ι}`. -/
theorem dot_translate_le_sub_one
    {S : Finset (ℤ × ℤ)} {m a : ℤ × ℤ}
    (hstrict : ∀ z ∈ S.erase a, Nivat.LE2.dot m z < Nivat.LE2.dot m a)
    {w : ℤ × ℤ} : ∀ z ∈ S.erase a,
      Nivat.LE2.dot m (z + (w - a)) ≤ Nivat.LE2.dot m w - 1 := by
  intro z hz
  have h := hstrict z hz
  rw [dot_translate_eq]
  omega

/-- **Goal 2c.2: the strict form of `translate_minus_apex_subset_of_argmax` (`SweepLines.lean:252`).**

The non-strict version needs `⟪m,w⟫ ≤ c` to conclude `⟪m, z + (w−a)⟫ ≤ c`.  With a *strict*
maximiser the hypothesis relaxes by one level: `w` may sit on the line `⟪m,w⟫ = c + 1`
immediately above the seed and its window still lands inside.  That one level is exactly what the
line-by-line induction of `:792-804` advances by at each step.

原文：b3_colle2.txt:794-798. -/
theorem translate_window_le_of_strict_argmax
    {S : Finset (ℤ × ℤ)} {m a : ℤ × ℤ} (_ha : a ∈ S)
    (hstrict : ∀ z ∈ S.erase a, Nivat.LE2.dot m z < Nivat.LE2.dot m a)
    {c : ℤ} {w : ℤ × ℤ} (hw : Nivat.LE2.dot m w ≤ c + 1) :
    ∀ z ∈ S.erase a, Nivat.LE2.dot m (z + (w - a)) ≤ c := by
  intro z hz
  have h := dot_translate_le_sub_one hstrict (w := w) z hz
  omega

/-! ## §2. The level-indexed lines -/

/-- The seed together with the level lines exhausts `ℤ²`: a point is either at level `≤ c` or at
level `c + 1 + i'` for exactly one `i' : ℕ`.  This is why `hKL` is free for this choice of
`lines`, for **any** set whatsoever — in particular for `chainFull B vl u' b₀ k`. -/
theorem mem_seed_union_lines (m : ℤ × ℤ) (c : ℤ) (z : ℤ × ℤ) :
    z ∈ {y : ℤ × ℤ | Nivat.LE2.dot m y ≤ c} ∪
      (⋃ i : ℕ, {y : ℤ × ℤ | Nivat.LE2.dot m y = c + 1 + i}) := by
  by_cases h : Nivat.LE2.dot m z ≤ c
  · exact Or.inl h
  · refine Or.inr (Set.mem_iUnion.mpr ⟨(Nivat.LE2.dot m z - c - 1).toNat, ?_⟩)
    show Nivat.LE2.dot m z = c + 1 + ((Nivat.LE2.dot m z - c - 1).toNat : ℤ)
    omega

/-- **`hwinL` in the shape `SweepLines.hbase_at_of_sweep_lines` (`:177`) consumes**, from strict
argmax alone.

原文：b3_colle2.txt:792-804.  `lines i` ↔ `A_i` (`:798-804`), `D` ↔ `H_B(ℓ)` (`:777`), and the
window landing in `D ∪ (⋃ i' < i, lines i')` ↔ "the knowledge of `T^u η` on `H_B(ℓ)` determines
uniquely `T^u η` on `A₁`" (`:798`), iterated.

The case split on the translated level is the entire proof: it is `≤ c + i` by the strict drop,
hence either `≤ c` (in `D`) or `= c + 1 + i'` with `i' < i`.  **At `i = 0` the union term is
empty and the surviving disjunct is exactly `∈ D`** — so this escapes
`L1SweepBridge.not_hwin_of_row_zero_levelConst` (`:749`) through `hstrict`, not through the
indexing, which `SweepLines.lean:214-232` already showed is not enough by itself. -/
theorem hwinL_of_strict_argmax
    {S : Finset (ℤ × ℤ)} {m a : ℤ × ℤ} (_ha : a ∈ S)
    (hstrict : ∀ z ∈ S.erase a, Nivat.LE2.dot m z < Nivat.LE2.dot m a) (c : ℤ) :
    ∀ i : ℕ, ∀ w ∈ {z : ℤ × ℤ | Nivat.LE2.dot m z = c + 1 + i}, ∀ z ∈ S.erase a,
      z + (w - a) ∈ {z : ℤ × ℤ | Nivat.LE2.dot m z ≤ c} ∪
        (⋃ i' ∈ {i' : ℕ | i' < i}, {z : ℤ × ℤ | Nivat.LE2.dot m z = c + 1 + i'}) := by
  intro i w hw z hz
  have hwlev : Nivat.LE2.dot m w = c + 1 + (i : ℤ) := hw
  have hdrop : Nivat.LE2.dot m (z + (w - a)) ≤ Nivat.LE2.dot m w - 1 :=
    dot_translate_le_sub_one hstrict (w := w) z hz
  by_cases hseed : Nivat.LE2.dot m (z + (w - a)) ≤ c
  · exact Or.inl hseed
  · refine Or.inr (Set.mem_biUnion
      (show (Nivat.LE2.dot m (z + (w - a)) - c - 1).toNat ∈ {i' : ℕ | i' < i} from ?_) ?_)
    · show (Nivat.LE2.dot m (z + (w - a)) - c - 1).toNat < i
      omega
    · show Nivat.LE2.dot m (z + (w - a))
        = c + 1 + ((Nivat.LE2.dot m (z + (w - a)) - c - 1).toNat : ℤ)
      omega

/-! ## §3. `hbase` at index `k`, reduced to `hD` -/

/-- **`hbase` from strict argmax: the only surviving hypothesis is `hD`.**

原文：b3_colle2.txt:792-804.  Instantiating `SweepLines.hbase_at_of_sweep_lines` (`:177`) with
`D := {z | ⟪m,z⟫ ≤ c}` and `lines i := {z | ⟪m,z⟫ = c + 1 + i}` discharges both of its geometric
binders: `hwinL` by `hwinL_of_strict_argmax`, and `hKL` by `mem_seed_union_lines`, which holds for
every subset of `ℤ²` and so uses no property of `chainFull`.

⚠ **Reading limit (读法 for the consumer, the statement itself is a kernel fact).** This does not
prove `hbase`; it says the line-by-line sweep costs exactly two things — a strict extreme vertex
for `𝒮_{φ_ι}` (`:792`, Wbox) and periodicity on the half plane `{z | ⟪m,z⟫ ≤ c}` (`hD`).  The
second is where the choice of seed region re-enters, and it is the only place it does. -/
theorem hbase_at_of_strict_argmax {ξ : Config ℤ} {e : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    {B : Set (ℤ × ℤ)} {vl u' b₀ : ℤ × ℤ} {cper : ℤ}
    -- 🔴 2026-09-21 集成者：同 `hbase_of_cone_halfStrip` 一族，换成 `:786`+`:790`+`:792` 的捆绑形状。
    (hS : Nivat.SweepLines.ReducedGeneratesAt ξ S a (cper • vl))
    (ha : a ∈ S) (hconv : Nivat.LatticeConvex (S.erase a))
    {m : ℤ × ℤ} (hstrict : ∀ z ∈ S.erase a, Nivat.LE2.dot m z < Nivat.LE2.dot m a)
    (k : ℕ) (c : ℤ)
    (hD : ∀ z ∈ {y : ℤ × ℤ | Nivat.LE2.dot m y ≤ c},
      (Nivat.T e ξ) z = Nivat.T (cper • vl) (Nivat.T e ξ) z) :
    Nivat.Colle41.PeriodOn (Nivat.T e ξ) (Nivat.ColleReg.chainFull B vl u' b₀ k) (cper • vl) :=
  Nivat.SweepLines.hbase_at_of_sweep_lines_reduced hS ha hconv k hD
    (fun i => {z : ℤ × ℤ | Nivat.LE2.dot m z = c + 1 + i})
    (hwinL_of_strict_argmax ha hstrict c)
    (fun z _ => mem_seed_union_lines m c z)

/-! ## §4. `hapex` (Figure 10) versus `hstrict`: the `t = 0` gap -/

/-- `⟪m, s•vl + t•u'⟫` expanded.  Helper for §4. -/
private theorem dot_apex_combo (m vl u' : ℤ × ℤ) (s t : ℤ) :
    Nivat.LE2.dot m (s • vl + t • u')
      = s * Nivat.LE2.dot m vl + t * Nivat.LE2.dot m u' := by
  simp only [Nivat.LE2.dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  ring

/-- **`hapex` gives the non-strict bound only.**

原文：b3_colle2.txt:794-798 (Figure 10) — "translate `𝒮_{φ_ι}` so that its extreme vertex sits
at `w`; every other point falls inside the cone".  Being inside the cone is
`z − a = s•vl + t•u'` with `s, t ≥ 0`.

**量词对应原文**:
- `z ∈ S.erase a` ↔ "every other point" of `𝒮_{φ_ι}`
- `s t : ℕ` ↔ the two non-negative cone coordinates along the two adjacent edge directions
  of the fan (`:770`)
- the conclusion `⟪m,z⟫ ≤ ⟪m,a⟫` ↔ `a` being *an* extreme vertex in the `m` direction

Arithmetic: `⟪m, z−a⟫ = s·⟪m,vl⟫ + t·⟪m,u'⟫ = s·0 + t·(−1) = −t ≤ 0`. -/
theorem dot_le_of_hapex {S : Finset (ℤ × ℤ)} {m vl u' a : ℤ × ℤ}
    (hperp : Nivat.LE2.dot m vl = 0) (hu' : Nivat.LE2.dot m u' = -1)
    (hapex : ∀ z ∈ S.erase a, ∃ s t : ℕ, z - a = (s : ℤ) • vl + (t : ℤ) • u') :
    ∀ z ∈ S.erase a, Nivat.LE2.dot m z ≤ Nivat.LE2.dot m a := by
  intro z hz
  obtain ⟨s, t, hst⟩ := hapex z hz
  have h : Nivat.LE2.dot m (z - a) = -(t : ℤ) := by
    rw [hst, dot_apex_combo, hperp, hu']
    ring
  rw [Nivat.LE2.dot_sub] at h
  omega

/-- **The `t = 0` gap is real: `hapex` does not imply `hstrict`.**

A point of `S` lying on the apex's own `vl`-line (`t = 0`, `s ≥ 1`) satisfies `hapex` and has
`⟪m,z⟫ = ⟪m,a⟫` exactly, because `⟪m,vl⟫ = 0` is precisely the transversality that makes the
seed `vl`-invariant.  So the step from Figure 10's cone condition to a *strict* maximiser is not
arithmetic; it needs a separate reason for `S` to have no second point on that line.

**Witness** (every hypothesis of the refuted implication is discharged below):
- `S := {(0,0), (1,0)}`, `a := (0,0)`, `m := (0,1)`, `vl := (1,0)`, `u' := (0,-1)`
- `⟪m,vl⟫ = 0`, `⟪m,u'⟫ = -1`, `a ∈ S`, `S.erase a = {(1,0)}` nonempty
- `hapex` holds at `s = 1, t = 0`; `⟪m,(1,0)⟫ = 0 = ⟪m,a⟫`, so `hstrict` fails.

⚠ 读法，非内核事实: `b3_colle2.txt:792` ("Lemma 2.6 implies that `𝒮_{φ_ι}` does not have any
edge parallel to `-ℓ` or `ℓ`") is the plausible source-side exclusion of this configuration, but
nothing here proves that it closes the gap — no lemma in this file uses it. -/
theorem not_hstrict_of_hapex :
    ∃ (S : Finset (ℤ × ℤ)) (m vl u' a : ℤ × ℤ),
      a ∈ S ∧ (S.erase a).Nonempty ∧
      Nivat.LE2.dot m vl = 0 ∧ Nivat.LE2.dot m u' = -1 ∧
      (∀ z ∈ S.erase a, ∃ s t : ℕ, z - a = (s : ℤ) • vl + (t : ℤ) • u') ∧
      ¬ (∀ z ∈ S.erase a, Nivat.LE2.dot m z < Nivat.LE2.dot m a) := by
  refine ⟨{((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ))}, ((0 : ℤ), (1 : ℤ)), ((1 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-1 : ℤ)), ((0 : ℤ), (0 : ℤ)), by decide, ⟨((1 : ℤ), (0 : ℤ)), by decide⟩,
    by decide, by decide, ?_, ?_⟩
  · intro z hz
    have hz' : z = ((1 : ℤ), (0 : ℤ)) := by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz.2 with h | h
      · exact absurd h hz.1
      · exact h
    exact ⟨1, 0, by rw [hz']; decide⟩
  · intro hcon
    exact absurd (hcon ((1 : ℤ), (0 : ℤ)) (by decide)) (by decide)

/-- **The repair: `hapex` with `t ≥ 1` does give `hstrict`.**

This is the hypothesis a producer should aim at.  It says every point of `𝒮_{φ_ι}` other than
the extreme vertex sits *strictly* inside the cone in the `u'` direction — equivalently, no second
point of `S` lies on the apex's `vl`-line.  Feeding this to `hbase_at_of_strict_argmax` (`:165`)
leaves `hD` as the sole obligation, exactly as before. -/
theorem strict_of_hapex_pos {S : Finset (ℤ × ℤ)} {m vl u' a : ℤ × ℤ}
    (hperp : Nivat.LE2.dot m vl = 0) (hu' : Nivat.LE2.dot m u' = -1)
    (hapex : ∀ z ∈ S.erase a, ∃ s t : ℕ, 0 < t ∧ z - a = (s : ℤ) • vl + (t : ℤ) • u') :
    ∀ z ∈ S.erase a, Nivat.LE2.dot m z < Nivat.LE2.dot m a := by
  intro z hz
  obtain ⟨s, t, htpos, hst⟩ := hapex z hz
  have h : Nivat.LE2.dot m (z - a) = -(t : ℤ) := by
    rw [hst, dot_apex_combo, hperp, hu']
    ring
  rw [Nivat.LE2.dot_sub] at h
  have : 0 < (t : ℤ) := by exact_mod_cast htpos
  omega

/-! ## §5. Over the cone: the assembly, the orientation, and the obstruction

原文：b3_colle2.txt:777-804.  `𝓡_{ι-1} := {g + t·v⃗_{ℓ_{ι-1}} : g ∈ H_B(ℓ), t ∈ ℤ₊}` (`:780`),
`A₁ := 𝓡_{ι-1} ∩ l₁` with `l₁ := ℓ_B^{(-)}` (`:796`), `l₂ := l₁^{(-)}` (`:802`), "proceeding
this way" (`:804`).  So the lines **descend** into the cone as the index grows, and the
translated generating set has its apex on the current line with the other points **above**, in
`H_B(ℓ) ∪ A₁ ∪ … ∪ A_{i-1}` (`:798`). -/

/-- `⟪n, b + s•vl + t•u'⟫` expanded.  Helper for §5. -/
private theorem dot_cone_pt (n b vl u' : ℤ × ℤ) (s t : ℤ) :
    Nivat.LE2.dot n (b + s • vl + t • u')
      = Nivat.LE2.dot n b + s * Nivat.LE2.dot n vl + t * Nivat.LE2.dot n u' := by
  simp only [Nivat.LE2.dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  ring

/-- **`hDsub`: the cone's upper part is the half-strip.**

原文：b3_colle2.txt:780 — the cone opens downward (`⟪nℓ,u'⟫ = -1`), so a cone point at or above
`B`'s own top level `cz` must have used `t = 0` steps along `u'`, i.e. it is `b + s•vl ∈ H_B(ℓ)`.

**量词对应原文**:
- `hperp : ⟪nℓ,vl⟫ = 0` ↔ `l_i` parallel to `ℓ` (Notation 3.3, `:406`)
- `hstep : ⟪nℓ,u'⟫ = -1` ↔ `l₂ := l₁^{(-)}` … one `u'`-step drops one line (`:802-804`)
- `hBtop : ∀ b ∈ B, ⟪nℓ,b⟫ ≤ cz` ↔ `ℓ_B` is a supporting line of `B` (`:472`)

Stated with `hBtop` rather than `cz = suppVal B nℓ`, which is strictly weaker and drops the
`B.Finite`/`B.Nonempty` binders that `suppVal` would need. -/
theorem cone_upper_subset_halfStrip {B : Set (ℤ × ℤ)} {vl u' nℓ : ℤ × ℤ} {cz : ℤ}
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hstep : Nivat.LE2.dot nℓ u' = -1)
    (hBtop : ∀ b ∈ B, Nivat.LE2.dot nℓ b ≤ cz) :
    Nivat.ConeRegion.coneRegion B vl u' ∩ {z | cz ≤ Nivat.LE2.dot nℓ z}
      ⊆ Nivat.LE2.halfStrip B vl := by
  rintro z ⟨hzc, hzlev⟩
  rw [Nivat.ConeRegion.mem_coneRegion_iff] at hzc
  obtain ⟨b, hb, s, t, rfl⟩ := hzc
  have hlev : cz ≤ Nivat.LE2.dot nℓ (b + (s : ℤ) • vl + (t : ℤ) • u') := hzlev
  rw [dot_cone_pt, hperp, hstep] at hlev
  have hbt := hBtop b hb
  have ht0 : t = 0 := by
    have : (t : ℤ) = 0 := by omega
    exact_mod_cast this
  subst ht0
  exact ⟨b, hb, s, by simp⟩

/-- **The assembly: `hbase` over the cone, with `hD` still on the paper's half-strip.**

原文：b3_colle2.txt:777-804.  `D` ↔ `H_B(ℓ)` seen inside the cone (`:777`), `lines i` ↔
`A_{i+1} = 𝓡_{ι-1} ∩ l_{i+1}` (`:796`, `:802`), `i : ℕ` ↔ "proceeding this way" (`:804`).

`SweepLines.hbase_at_of_sweep_lines` (`:177`) takes `D` and `lines` as free parameters, so
`hD` does **not** have to be restated on the cone: it stays on `H_B(ℓ)` exactly as the source
has it, and `hDsub` transports it.  `cone_upper_subset_halfStrip` produces `hDsub` from
`hperp`/`hstep`/`hBtop`.

⚠ **读法，非内核事实** for the consumer: this is the wiring only.  `hwinL` and `hKL` are
hypotheses here and neither is discharged; `not_hwinL_cone_ascending` below shows `hwinL` in
this orientation is **false** for a general `B`, so a producer must add hypotheses. -/
theorem hbase_of_cone_argmax {ξ : Config ℤ} {e : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    {B : Set (ℤ × ℤ)} {vl u' b₀ nℓ : ℤ × ℤ} {c cz : ℤ}
    -- 🔴 2026-09-21 集成者：`GeneratesAt ξ S a` 换成原文 `:786`+`:790`+`:792` 的捆绑形状。
    -- 原文从未断言 `𝒮_{φ_ι}` 生成 `ξ` 本身，只断言它在 `ZMod p` 里生成差 `η − η̄_{ι₀}`。
    (hS : Nivat.SweepLines.ReducedGeneratesAt ξ S a (c • vl))
    (ha : a ∈ S) (hconv : Nivat.LatticeConvex (S.erase a)) (k : ℕ)
    (hD : ∀ z ∈ Nivat.LE2.halfStrip B vl,
      (Nivat.T e ξ) z = Nivat.T (c • vl) (Nivat.T e ξ) z)
    (hDsub : Nivat.ConeRegion.coneRegion B vl u' ∩ {z | cz ≤ Nivat.LE2.dot nℓ z}
      ⊆ Nivat.LE2.halfStrip B vl)
    (hwinL : ∀ i : ℕ, ∀ w ∈ (Nivat.ConeRegion.coneRegion B vl u' ∩
        {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)}), ∀ z ∈ S.erase a,
      z + (w - a) ∈ (Nivat.ConeRegion.coneRegion B vl u' ∩
          {y | cz ≤ Nivat.LE2.dot nℓ y}) ∪
        (⋃ i' ∈ {i' : ℕ | i' < i}, (Nivat.ConeRegion.coneRegion B vl u' ∩
          {y | Nivat.LE2.dot nℓ y = cz - 1 - (i' : ℤ)})))
    (hKL : Nivat.ColleReg.chainFull B vl u' b₀ k ⊆
      (Nivat.ConeRegion.coneRegion B vl u' ∩ {y | cz ≤ Nivat.LE2.dot nℓ y}) ∪
        (⋃ i : ℕ, (Nivat.ConeRegion.coneRegion B vl u' ∩
          {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)}))) :
    Nivat.Colle41.PeriodOn (Nivat.T e ξ) (Nivat.ColleReg.chainFull B vl u' b₀ k) (c • vl) :=
  Nivat.SweepLines.hbase_at_of_sweep_lines_reduced hS ha hconv k (fun z hz => hD z (hDsub hz))
    (fun i => Nivat.ConeRegion.coneRegion B vl u' ∩
      {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)})
    hwinL hKL

/-- **The orientation answer: Lemma 2.6's producer gives the level-MAXIMUM, and `m := -nℓ`
turns it into the minimum.**

`ApexUnique.exists_strict_argmax_of_no_edge_parallel` (`ApexUnique.lean:119`) concludes
`∀ z ∈ S.erase a, ⟪m,z⟫ < ⟪m,a⟫` — the strict **max** of `⟪m,·⟫`.  Descending lines
(`cz - 1 - i`, `:796-804`) need the apex to be the level **min**, so the instantiation is
`m := -nℓ`.  This is not a negated hypothesis: `m` is a free parameter of that theorem,
constrained only by `Primitive m` and `⟪m,vl⟫ = 0`, and both transfer to `-nℓ`.

原文：b3_colle2.txt:792 — `hno` is "`𝒮_{φ_ι}` does not have any edge parallel to `-ℓ` or `ℓ`";
it is symmetric in the sign of the normal, which is why the same `hno` serves both ends. -/
theorem exists_strict_argmin_of_no_edge_parallel
    {S : Finset (ℤ × ℤ)} (hne : S.Nonempty) {nℓ vl : ℤ × ℤ}
    (hprim : Nivat.Primitive nℓ) (hperp : Nivat.LE2.dot nℓ vl = 0)
    (hno : ∀ n ∈ Nivat.LE2.E (↑S : Set (ℤ × ℤ)), Nivat.LE2.dot n vl ≠ 0) :
    ∃ a ∈ S, ∀ z ∈ S.erase a, Nivat.LE2.dot nℓ a < Nivat.LE2.dot nℓ z := by
  have hprim' : Nivat.Primitive (-nℓ) := by
    obtain ⟨p, q, hpq⟩ := hprim
    exact ⟨-p, -q, by simp only [Prod.fst_neg, Prod.snd_neg]; linear_combination hpq⟩
  obtain ⟨a, ha, hmax⟩ :=
    Nivat.ApexUnique.exists_strict_argmax_of_no_edge_parallel hne hprim'
      (by rw [Nivat.LE2.dot_neg_left, hperp]; ring) hno
  refine ⟨a, ha, fun z hz => ?_⟩
  have h := hmax z hz
  rw [Nivat.LE2.dot_neg_left, Nivat.LE2.dot_neg_left] at h
  linarith

/-- **🔴 `hwinL` over the cone, in the descending orientation, is FALSE for a general `B`.**

The cone is bounded **above**: every point of `coneRegion B vl u'` has `⟪nℓ,·⟫ ≤ cz`
(`ConeRegion.dot_le_suppVal_of_mem_coneRegion`, `:153`).  Descending lines force the
translated window to move **up**, and a generator sitting two levels above the apex sends the
window above `cz` when the apex is on line `i = 0` — out of the cone entirely, hence out of
`D ∪ ⋃_{i' < i} lines` whatever `D` is taken to be inside the cone.

**Witness** (every hypothesis of the refuted statement discharged below):
- `B := {(0,0)}`, `vl := (1,0)`, `u' := (0,-1)`, `nℓ := (0,1)`, `cz := 0`
- `S := {(0,0), (0,2)}`, `a := (0,0)` — the strict level **minimum**, the orientation the
  descending lines require
- `i := 0`, `w := (0,-1) ∈ coneRegion ∩ {level = cz - 1}`
- `z := (0,2)`; `z + (w - a) = (0,1)`, at level `1 > cz`, and `(0,1) ∉ coneRegion` because the
  cone is `{(s,-t) : s,t ∈ ℕ}`.

⚠ This refutes the *shape*, not the paper.  `:798` places the non-apex points of `Ŝ_{φ_ι}` in
`H_B(ℓ) ∪ A₁ ∪ … ∪ A_{i-1}`, and for `i = 0` that is `H_B(ℓ)` alone — so the source is
implicitly asserting that the translate does not overshoot `ℓ_B`.  What is missing is the
hypothesis that supplies this; it is **not** derivable from `hperp`/`hstep`/strict argmin.
读法，非内核事实: I do not claim to know which hypothesis the source intends. -/
theorem not_hwinL_cone_ascending :
    ∃ (B : Set (ℤ × ℤ)) (S : Finset (ℤ × ℤ)) (vl u' nℓ a : ℤ × ℤ) (cz : ℤ),
      B.Finite ∧ B.Nonempty ∧
      Nivat.LE2.dot nℓ vl = 0 ∧ Nivat.LE2.dot nℓ u' = -1 ∧
      (∀ b ∈ B, Nivat.LE2.dot nℓ b ≤ cz) ∧
      a ∈ S ∧ (∀ z ∈ S.erase a, Nivat.LE2.dot nℓ a < Nivat.LE2.dot nℓ z) ∧
      ¬ (∀ i : ℕ, ∀ w ∈ (Nivat.ConeRegion.coneRegion B vl u' ∩
            {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)}), ∀ z ∈ S.erase a,
          z + (w - a) ∈ (Nivat.ConeRegion.coneRegion B vl u' ∩
              {y | cz ≤ Nivat.LE2.dot nℓ y}) ∪
            (⋃ i' ∈ {i' : ℕ | i' < i}, (Nivat.ConeRegion.coneRegion B vl u' ∩
              {y | Nivat.LE2.dot nℓ y = cz - 1 - (i' : ℤ)}))) := by
  refine ⟨{((0 : ℤ), (0 : ℤ))}, {((0 : ℤ), (0 : ℤ)), ((0 : ℤ), (2 : ℤ))},
    ((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (-1 : ℤ)), ((0 : ℤ), (1 : ℤ)), ((0 : ℤ), (0 : ℤ)), 0,
    Set.finite_singleton _, ⟨((0 : ℤ), (0 : ℤ)), rfl⟩, by decide, by decide, ?_, by decide,
    ?_, ?_⟩
  · intro b hb
    have hb0 : b = ((0 : ℤ), (0 : ℤ)) := by simpa using hb
    rw [hb0]
    decide
  · intro z hz
    have hz2 : z = ((0 : ℤ), (2 : ℤ)) := by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz.2 with h | h
      · exact absurd h hz.1
      · exact h
    rw [hz2]
    decide
  · intro hcon
    have hw : ((0 : ℤ), (-1 : ℤ)) ∈ (Nivat.ConeRegion.coneRegion
        ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (-1 : ℤ)) ∩
        {y | Nivat.LE2.dot ((0 : ℤ), (1 : ℤ)) y = (0 : ℤ) - 1 - ((0 : ℕ) : ℤ)}) := by
      refine ⟨Nivat.ConeRegion.mem_coneRegion_iff.mpr
        ⟨((0 : ℤ), (0 : ℤ)), rfl, 0, 1, by decide⟩, ?_⟩
      show Nivat.LE2.dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ))
        = (0 : ℤ) - 1 - ((0 : ℕ) : ℤ)
      decide
    have h := hcon 0 _ hw ((0 : ℤ), (2 : ℤ)) (by decide)
    have hpt : ((0 : ℤ), (2 : ℤ)) + (((0 : ℤ), (-1 : ℤ)) - ((0 : ℤ), (0 : ℤ)))
        = ((0 : ℤ), (1 : ℤ)) := by decide
    rw [hpt] at h
    rcases h with hin | hin
    · obtain ⟨hc, -⟩ := hin
      rw [Nivat.ConeRegion.mem_coneRegion_iff] at hc
      obtain ⟨b, hb, s, t, heq⟩ := hc
      have hb0 : b = ((0 : ℤ), (0 : ℤ)) := by simpa using hb
      subst hb0
      have h2 := congrArg Prod.snd heq
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] at h2
      omega
    · obtain ⟨i', hi', -⟩ := Set.mem_iUnion₂.mp hin
      exact absurd (show i' < 0 from hi') (Nat.not_lt_zero i')

/-- **The refuting witness survives Lemma 2.6.**

The set `{(0,0), (0,2)}` used in `not_hwinL_cone_ascending` has no edge parallel to
`vl = (1,0)`, so it is *not* excluded by `b3_colle2.txt:792` and the only producer we have
for the apex — `exists_strict_argmin_of_no_edge_parallel` (`:363`) — applies to it.

Proof: its two points differ by `(0,2)`, so an edge normal `n` must satisfy `2·n₂ = 0`, hence
`n₂ = 0`; `Prim n` then forces `n₁ ≠ 0`, and `⟪n,(1,0)⟫ = n₁ ≠ 0`. -/
theorem no_edge_parallel_witness :
    ∀ n ∈ Nivat.LE2.E (↑({((0 : ℤ), (0 : ℤ)), ((0 : ℤ), (2 : ℤ))} : Finset (ℤ × ℤ)) :
      Set (ℤ × ℤ)), Nivat.LE2.dot n ((1 : ℤ), (0 : ℤ)) ≠ 0 := by
  intro n hn hdot
  obtain ⟨hprim, z, hz, w, hw, hzw⟩ := hn
  have h0 : Nivat.LE2.dot n (w - z) = 0 := Nivat.LE2.dot_sub_eq_zero_of_mem_face hz hw
  have hzS : z = ((0 : ℤ), (0 : ℤ)) ∨ z = ((0 : ℤ), (2 : ℤ)) := by simpa using hz.1
  have hwS : w = ((0 : ℤ), (0 : ℤ)) ∨ w = ((0 : ℤ), (2 : ℤ)) := by simpa using hw.1
  have hn2 : n.2 = 0 := by
    simp only [Nivat.LE2.dot, Prod.fst_sub, Prod.snd_sub] at h0
    rcases hzS with rfl | rfl <;> rcases hwS with rfl | rfl <;> simp_all
  have hn1 : n.1 = 0 := by simpa [Nivat.LE2.dot] using hdot
  exact hprim.ne_zero (Prod.ext hn1 hn2)

/-- **The paper-faithful assembly: `D` is `H_B(ℓ)` itself, no `hDsub`.**

原文：b3_colle2.txt:777-804.  This is `hbase_of_cone_argmax` with `D := H_B(ℓ)` taken literally
rather than as a level-slice of the cone, which is what `:798` actually says
("the knowledge of `T^u η` on `H_B(ℓ)` determines uniquely `T^u η` on `A₁`").

**量词对应原文**:
- `D` ↔ `H_B(ℓ)` (`:777`), not a level set — the half-strip is a *positional* region
- `lines i` ↔ `A_{i+1} = 𝓡_{ι-1} ∩ l_{i+1}` (`:796`, `:802`)
- `cz` ↔ the level of `ℓ_B`, with `l₁ := ℓ_B^{(-)}` one line below it (`:796`)

Strictly stronger than `hbase_of_cone_argmax` (`:328`): it has one binder fewer, since `hD`
no longer has to be transported.  `u'` is a free variable and no hypothesis constrains it, so
this survives the shear `u' ↦ u' - K•vl` of `L1StraddleWedge.exists_corner_shear`. -/
theorem hbase_of_cone_halfStrip {ξ : Config ℤ} {e : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    {B : Set (ℤ × ℤ)} {vl u' b₀ nℓ : ℤ × ℤ} {c cz : ℤ}
    -- 🔴 2026-09-21 集成者：`GeneratesAt ξ S a` 换成原文 `:786`+`:790`+`:792` 的捆绑形状。
    -- 原文从未断言 `𝒮_{φ_ι}` 生成 `ξ` 本身，只断言它在 `ZMod p` 里生成差 `η − η̄_{ι₀}`。
    (hS : Nivat.SweepLines.ReducedGeneratesAt ξ S a (c • vl))
    (ha : a ∈ S) (hconv : Nivat.LatticeConvex (S.erase a)) (k : ℕ)
    (hD : ∀ z ∈ Nivat.LE2.halfStrip B vl,
      (Nivat.T e ξ) z = Nivat.T (c • vl) (Nivat.T e ξ) z)
    (hwinL : ∀ i : ℕ, ∀ w ∈ (Nivat.ConeRegion.coneRegion B vl u' ∩
        {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)}), ∀ z ∈ S.erase a,
      z + (w - a) ∈ Nivat.LE2.halfStrip B vl ∪
        (⋃ i' ∈ {i' : ℕ | i' < i}, (Nivat.ConeRegion.coneRegion B vl u' ∩
          {y | Nivat.LE2.dot nℓ y = cz - 1 - (i' : ℤ)})))
    (hKL : Nivat.ColleReg.chainFull B vl u' b₀ k ⊆
      Nivat.LE2.halfStrip B vl ∪
        (⋃ i : ℕ, (Nivat.ConeRegion.coneRegion B vl u' ∩
          {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)}))) :
    Nivat.Colle41.PeriodOn (Nivat.T e ξ) (Nivat.ColleReg.chainFull B vl u' b₀ k) (c • vl) :=
  Nivat.SweepLines.hbase_at_of_sweep_lines_reduced hS ha hconv k hD
    (fun i => Nivat.ConeRegion.coneRegion B vl u' ∩
      {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)})
    hwinL hKL

/-- **The level-necessary condition for `hwinL`, and hence the exact size of the overshoot.**

If the translated window is to land in `H_B(ℓ)` — whose levels are exactly the levels of `B`,
since `⟪nℓ,vl⟫ = 0` — then its level must be at most `B`'s top level.  With `w` on line `i`
(level `cz - 1 - i`) and `z` at height `d := ⟪nℓ,z⟫ - ⟪nℓ,a⟫` above the apex, the window sits at
level `cz - 1 - i + d`, so the requirement is

    d ≤ i + 1 + (ctop - cz).

**This is why `B` being a single point refutes and a tall `B` may not.**  `ctop - cz` is `B`'s
height in the `nℓ` direction; Definition 3.2 (`:402`) forces `B` to have positive area and to
dominate `𝒮_φ` edge by edge, so an enveloped `B` is not short.  The binding case is `i = 0`.

原文：b3_colle2.txt:796-798.  读法，非内核事实 for the consumer: this is **necessary**, not
sufficient — `H_B(ℓ)` is a positional region, so landing at a legal level does not put the
window inside it. -/
theorem level_le_of_mem_halfStrip {B : Set (ℤ × ℤ)} {vl nℓ : ℤ × ℤ} {ctop : ℤ}
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hBtop : ∀ b ∈ B, Nivat.LE2.dot nℓ b ≤ ctop) :
    ∀ z ∈ Nivat.LE2.halfStrip B vl, Nivat.LE2.dot nℓ z ≤ ctop := by
  rintro z ⟨b, hb, t, rfl⟩
  have hd : Nivat.LE2.dot nℓ (b + (t : ℤ) • vl)
      = Nivat.LE2.dot nℓ b + (t : ℤ) * Nivat.LE2.dot nℓ vl := by
    simp only [Nivat.LE2.dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    ring
  rw [hd, hperp]
  have := hBtop b hb
  omega

/-! ## §6. `hwinL` over the cone, split into `hstrict` (proved) and `hfit` (envelopedness) -/

/-- **`hwinL` for the descending cone lines, from a strict level-minimum plus cone-fit.**

原文：b3_colle2.txt:777-804.  The two hypotheses are the two things the source actually uses at
this step, separated so that exactly one of them is still owed:

- `hstrict` ↔ `:792`, "Lemma 2.6 implies that `𝒮_{φ_ι}` does not have any edge parallel to `-ℓ`
  or `ℓ`" — no edge on the extreme face means the extreme vertex is unique.  Here `a` is the
  **level-minimum** because the lines descend (`l₁ := ℓ_B^{(-)}`, `l₂ := l₁^{(-)}`, `:796`,
  `:802`), so the translate that places `a` at `w` moves the rest of the seed **up**.
  **This one is already produced unconditionally** by
  `exists_strict_argmin_of_no_edge_parallel` (`:363`).
- `hfit` ↔ `:798`, "the knowledge of `T^u η` on `H_B(ℓ)` determines uniquely `T^u η` on `A₁`",
  whose standing justification is `:777` — `B` is `E(𝒮_φ)`-enveloped in the sense of
  Definition 3.2 (`:402`).  The `∀ w ∈ coneRegion` is Collé's: `Ŝ_{φ_ι}` is placed at an
  arbitrary point of `𝓡_{ι-1}` (`:780`), not at a distinguished one.
  **This one is owed, and is the whole residual of the cone route.**

**量词对应原文**:
- `i : ℕ` ↔ "proceeding this way, we get by induction" (`:804`)
- `lines i = 𝓡_{ι-1} ∩ l_{i+1}` ↔ `A_{i+1}` (`:794-798`, `:802`)
- `D = 𝓡_{ι-1} ∩ {level ≥ cz}` ↔ `H_B(ℓ)` inside the cone (`:777-780`), `cz` the level of `ℓ_B`
- `z ∈ S.erase a` ↔ the non-apex points of `𝒮_{φ_ι}`
- `z + (w - a)` ↔ the translate of Figure 10 placing the extreme vertex at `w`

**Why this is the right split.**  `not_hwinL_cone_ascending` (`:400`) refutes the same conclusion
from `hstrict` *alone*: its witness `z - a = (0,2)` under `vl = (1,0)`, `u' = (0,-1)` needs
`t = -2`, so the seed leaves the cone sideways and no level argument can save it.  What that
refutation isolates is precisely `hfit`, and `hfit` is where envelopedness — never used anywhere
on the cone route so far — has to enter.  Given `hfit`, the rest is the level arithmetic of
`hwinL_of_strict_argmax` (`:136`) with the sign reversed and a cone component carried along.

⚠ `_hnℓ_vl` and `_hnℓ_u'` are **not used**: the arithmetic below is pure linearity in `nℓ`.  They
are kept in the signature because they are what makes the statement *meaningful* — transversality
(`⟪nℓ,vl⟫ = 0`) is what makes the lines `vl`-invariant and hence `hD` satisfiable, and
`⟪nℓ,u'⟫ = -1` is what makes the cone occupy every level below `cz` so that `lines` is a cover
(`LineIndex.coneRegion_subset_union_lines`, `:183`).  Dropping them would let a caller instantiate
`nℓ := 0` and get a vacuous instance. -/
theorem hwinL_cone_of_hstrict_of_hfit
    {B : Set (ℤ × ℤ)} {vl u' nℓ : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {cz : ℤ}
    (hstrict : ∀ z ∈ S.erase a, Nivat.LE2.dot nℓ a < Nivat.LE2.dot nℓ z)
    (_hnℓ_vl : Nivat.LE2.dot nℓ vl = 0) (_hnℓ_u' : Nivat.LE2.dot nℓ u' = -1)
    (hfit : ∀ w ∈ Nivat.ConeRegion.coneRegion B vl u', ∀ z ∈ S.erase a,
      z + (w - a) ∈ Nivat.ConeRegion.coneRegion B vl u') :
    ∀ i : ℕ, ∀ w ∈ (Nivat.ConeRegion.coneRegion B vl u' ∩
        {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)}), ∀ z ∈ S.erase a,
      z + (w - a) ∈ (Nivat.ConeRegion.coneRegion B vl u' ∩ {y | cz ≤ Nivat.LE2.dot nℓ y}) ∪
        (⋃ i' ∈ {i' : ℕ | i' < i}, (Nivat.ConeRegion.coneRegion B vl u' ∩
          {y | Nivat.LE2.dot nℓ y = cz - 1 - (i' : ℤ)})) := by
  intro i w hw z hz
  have hwlev : Nivat.LE2.dot nℓ w = cz - 1 - (i : ℤ) := hw.2
  have hrise := hstrict z hz
  have heq : Nivat.LE2.dot nℓ (z + (w - a))
      = Nivat.LE2.dot nℓ z + Nivat.LE2.dot nℓ w - Nivat.LE2.dot nℓ a :=
    dot_translate_eq nℓ z w a
  have hmem : z + (w - a) ∈ Nivat.ConeRegion.coneRegion B vl u' := hfit w hw.1 z hz
  by_cases hup : cz ≤ Nivat.LE2.dot nℓ (z + (w - a))
  · exact Or.inl ⟨hmem, hup⟩
  · refine Or.inr (Set.mem_biUnion
      (show (cz - 1 - Nivat.LE2.dot nℓ (z + (w - a))).toNat ∈ {i' : ℕ | i' < i} from ?_)
      ⟨hmem, ?_⟩)
    · show (cz - 1 - Nivat.LE2.dot nℓ (z + (w - a))).toNat < i
      omega
    · show Nivat.LE2.dot nℓ (z + (w - a))
        = cz - 1 - ((cz - 1 - Nivat.LE2.dot nℓ (z + (w - a))).toNat : ℤ)
      omega

/-! ## §7. 🔴 `hfit` is false whenever `B` is finite -/

/-- **`hfit` cannot hold for a finite nonempty `B`.**

This is a satisfiability check on `hwinL_cone_of_hstrict_of_hfit` (`:578`), not a weakening of
`hfit` and not an attempt to prove it: the conjunction `hstrict ∧ hfit` is **contradictory** as
soon as `B` is finite and nonempty, so the residual the split isolates is unreachable in that
regime.

**Proof, in one line.**  `⟪nℓ,u'⟫ = -1` and `⟪nℓ,vl⟫ = 0` make every cone point sit at level
`⟪nℓ,b⟫ - t ≤ suppVal B nℓ` (`ConeRegion.dot_le_suppVal_of_mem_coneRegion`, `:153`).  Take `w`
to be a point of `B` attaining that support value — it is in the cone with `s = t = 0`.  Then
`hstrict` puts `z + (w - a)` strictly **above** `suppVal B nℓ`, so it is not in the cone, and
`hfit` fails at that `w`.  The binding instance is the top level of `B`; nothing below it is
used.

**Every hypothesis of the refuted statement is discharged here** (`PROTOCOL.md` §7): the
refuted claim is `hfit` under exactly the ambient hypotheses of `:578` plus `B.Finite`,
`B.Nonempty`, `(S.erase a).Nonempty`.  The first two are not in `:578`; **that is the whole
content of this theorem** — `:578` is consistent only for infinite (or empty) `B`.

原文：b3_colle2.txt:777, :780.  `𝓡_{ι-1}` is built from `H_B(ℓ)` by sweeping in `+v⃗_{ℓ_{ι-1}}`
only, so it is bounded above in the transverse direction by `B` itself; Definition 3.2 (`:402`)
makes `B` a bounded lattice polygon.  Envelopedness therefore **cannot** rescue `hfit` in the
descending orientation — it constrains `B`'s shape, not its boundedness, and boundedness is what
kills it. -/
theorem not_hfit_of_finite
    {B : Set (ℤ × ℤ)} {vl u' nℓ : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    (hfin : B.Finite) (hne : B.Nonempty)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hstep : Nivat.LE2.dot nℓ u' = -1)
    (hSne : (S.erase a).Nonempty)
    (hstrict : ∀ z ∈ S.erase a, Nivat.LE2.dot nℓ a < Nivat.LE2.dot nℓ z) :
    ¬ (∀ w ∈ Nivat.ConeRegion.coneRegion B vl u', ∀ z ∈ S.erase a,
        z + (w - a) ∈ Nivat.ConeRegion.coneRegion B vl u') := by
  intro hfit
  obtain ⟨z, hz⟩ := hSne
  obtain ⟨b₀, hb₀, hb₀eq⟩ := Nivat.LE2.exists_suppVal_eq hfin hne nℓ
  have hw : b₀ ∈ Nivat.ConeRegion.coneRegion B vl u' := by
    rw [Nivat.ConeRegion.mem_coneRegion_iff]
    exact ⟨b₀, hb₀, 0, 0, by simp⟩
  have hle := Nivat.ConeRegion.dot_le_suppVal_of_mem_coneRegion hfin hne hperp hstep
    (hfit b₀ hw z hz)
  have heq : Nivat.LE2.dot nℓ (z + (b₀ - a))
      = Nivat.LE2.dot nℓ z + Nivat.LE2.dot nℓ b₀ - Nivat.LE2.dot nℓ a :=
    dot_translate_eq nℓ z b₀ a
  have hrise := hstrict z hz
  omega

/-! ## §8. `hwinL` over the half-strip: lines below the strip, two geometric residuals -/

/-- **`hwinL` for `hbase_of_cone_halfStrip` (`:489`), from `hstrict` plus two level-restricted
geometric containments.**

原文：b3_colle2.txt:414, :784, :794-798.  The three source facts that fix the shape:
- `:414` — `H_B(ℓ) := {g + t·v⃗_ℓ : g ∈ B, t ∈ ℤ₊}`, based at **`B`**.
- `:784` — `𝓡_{ι-1} := {g + t·v⃗_{ℓ_{ι-1}} : g ∈ H_B(ℓ), t ∈ ℤ₊}`, based at **`H_B(ℓ)`**.
- `:798` — the extension is *to* `H_B(ℓ) ∪ A₁`, i.e. the translated seed must land in
  **`H_B(ℓ)`**, not merely in `𝓡_{ι-1}`.

Since `⟪nℓ,vl⟫ = 0`, `H_B(ℓ)` occupies exactly the levels of `B`, a band; the descent
`l₁, l₂, …` starts one level below the band's **bottom**, so the intended instantiation is
`cz := ` a lower bound for `⟪nℓ,·⟫` on `B`.

⚠ **`cz` is left a free variable because `infVal` does not exist in the tree** — `grep -rn
"infVal" Nivat/` returns nothing, and I did not define one (a `def` with a single consumer in
one off-chain file is the pattern `PROTOCOL.md` §20 warns about).  A free `cz` is strictly
more general: instantiate at any lower bound.  Picking a *bad* `cz` is self-policing rather
than dangerous, because a `cz` above `B`'s bottom simply makes `hstrip` undischargeable — it
cannot make the conclusion vacuously available.

**量词对应原文**:
- `i : ℕ` ↔ "proceeding this way, we get by induction" (`:804`)
- `w ∈ 𝓡_{ι-1} ∩ l_{i+1}` ↔ `A_{i+1}` (`:794`, `:802`); the level constraint on `w` is
  **carried into both residuals** and is not discarded
- `z + (w - a)` ↔ Figure 10's translate placing the extreme vertex of `𝒮_{φ_ι}` at `w`
- `hstrict` ↔ `:792` (Lemma 2.6, no edge parallel to `±ℓ`), with `a` the level-**minimum**
  because the lines descend — produced unconditionally by
  `exists_strict_argmin_of_no_edge_parallel` (`:363`)

**The split, and why the two residuals are the honest ones.**  `hstrict` alone gives the level
rise `⟪nℓ, z+(w−a)⟫ = ⟪nℓ,w⟫ + d` with `d ≥ 1`, which makes the case split exhaustive: below
`cz` the translate is on line `i − d`, which is a legal index because `d ≥ 1` gives `i − d < i`
and `⟪nℓ,·⟫ ≤ cz − 1` gives `i − d ≥ 0`.  What `hstrict` cannot give is *membership*: staying
in the cone on the lower branch (`hcone`), and landing in the strip on the upper one
(`hstrip`).  Those two are the residual, and both are geometry about `B`, not arithmetic.

🔴 **Both residuals restrict `w` to `⟪nℓ,w⟫ < cz`, and that restriction is load-bearing.**
Dropping it reproduces `not_hfit_of_finite` (`:633`): its refuting `w` is a top-level point of
`B`, which lies in `coneRegion` but on **no** line below the strip.  An unrestricted `hstrip`
is false for every finite nonempty `B` by the same three-line argument.  I have not found a
refutation of either residual in the restricted form. -/
theorem hwinL_cone_halfStrip_of_hstrict_of_geom
    {B : Set (ℤ × ℤ)} {vl u' nℓ : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} {cz : ℤ}
    (hstrict : ∀ z ∈ S.erase a, Nivat.LE2.dot nℓ a < Nivat.LE2.dot nℓ z)
    (hcone : ∀ w ∈ Nivat.ConeRegion.coneRegion B vl u', Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ S.erase a, Nivat.LE2.dot nℓ (z + (w - a)) < cz →
        z + (w - a) ∈ Nivat.ConeRegion.coneRegion B vl u')
    (hstrip : ∀ w ∈ Nivat.ConeRegion.coneRegion B vl u', Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ S.erase a, cz ≤ Nivat.LE2.dot nℓ (z + (w - a)) →
        z + (w - a) ∈ Nivat.LE2.halfStrip B vl) :
    ∀ i : ℕ, ∀ w ∈ (Nivat.ConeRegion.coneRegion B vl u' ∩
        {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)}), ∀ z ∈ S.erase a,
      z + (w - a) ∈ Nivat.LE2.halfStrip B vl ∪
        (⋃ i' ∈ {i' : ℕ | i' < i}, (Nivat.ConeRegion.coneRegion B vl u' ∩
          {y | Nivat.LE2.dot nℓ y = cz - 1 - (i' : ℤ)})) := by
  intro i w hw z hz
  have hwlev : Nivat.LE2.dot nℓ w = cz - 1 - (i : ℤ) := hw.2
  have hrise := hstrict z hz
  have heq : Nivat.LE2.dot nℓ (z + (w - a))
      = Nivat.LE2.dot nℓ z + Nivat.LE2.dot nℓ w - Nivat.LE2.dot nℓ a :=
    dot_translate_eq nℓ z w a
  have hwlt : Nivat.LE2.dot nℓ w < cz := by omega
  by_cases hup : cz ≤ Nivat.LE2.dot nℓ (z + (w - a))
  · exact Or.inl (hstrip w hw.1 hwlt z hz hup)
  · push Not at hup
    refine Or.inr (Set.mem_biUnion
      (show (cz - 1 - Nivat.LE2.dot nℓ (z + (w - a))).toNat ∈ {i' : ℕ | i' < i} from ?_)
      ⟨hcone w hw.1 hwlt z hz hup, ?_⟩)
    · show (cz - 1 - Nivat.LE2.dot nℓ (z + (w - a))).toNat < i
      omega
    · show Nivat.LE2.dot nℓ (z + (w - a))
        = cz - 1 - ((cz - 1 - Nivat.LE2.dot nℓ (z + (w - a))).toNat : ℤ)
      omega

/-- **The composition: `hbase` from `hD`, `hKL`, `hstrict`, and the two geometric residuals.**

This is `hbase_of_cone_halfStrip` (`:489`) with its `hwinL` binder replaced by the split of
`hwinL_cone_halfStrip_of_hstrict_of_geom` above, so that what a caller owes is exactly:

| binder | status |
|---|---|
| `hS`, `ha`, `hconv` | the generating-set data, supplied at the call site |
| `hstrict` | **produced** — `exists_strict_argmin_of_no_edge_parallel` (`:363`) |
| `hcone`, `hstrip` | **the residual** — geometry of `B`, level-restricted |
| `hD` | periodicity on `H_B(ℓ)` (`:798`) |
| `hKL` | `chainFull` covered by the strip and the lines |

原文：b3_colle2.txt:792-804.

`u'` is a free variable and no hypothesis constrains it, so this survives the shear
`u' ↦ u' - K • vl` that `L1StraddleWedge.exists_corner_shear` (`:423`) hands to
`WedgeAssemble.nonempty_wedgeResidualR_of_hbase_at_shear`. -/
theorem hbase_of_cone_halfStrip_of_geom {ξ : Config ℤ} {e : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    {B : Set (ℤ × ℤ)} {vl u' b₀ nℓ : ℤ × ℤ} {c cz : ℤ}
    -- 🔴 2026-09-21 集成者：`GeneratesAt ξ S a` 换成原文 `:786`+`:790`+`:792` 的捆绑形状。
    -- 原文从未断言 `𝒮_{φ_ι}` 生成 `ξ` 本身，只断言它在 `ZMod p` 里生成差 `η − η̄_{ι₀}`。
    (hS : Nivat.SweepLines.ReducedGeneratesAt ξ S a (c • vl))
    (ha : a ∈ S) (hconv : Nivat.LatticeConvex (S.erase a)) (k : ℕ)
    (hD : ∀ z ∈ Nivat.LE2.halfStrip B vl,
      (Nivat.T e ξ) z = Nivat.T (c • vl) (Nivat.T e ξ) z)
    (hstrict : ∀ z ∈ S.erase a, Nivat.LE2.dot nℓ a < Nivat.LE2.dot nℓ z)
    (hcone : ∀ w ∈ Nivat.ConeRegion.coneRegion B vl u', Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ S.erase a, Nivat.LE2.dot nℓ (z + (w - a)) < cz →
        z + (w - a) ∈ Nivat.ConeRegion.coneRegion B vl u')
    (hstrip : ∀ w ∈ Nivat.ConeRegion.coneRegion B vl u', Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ S.erase a, cz ≤ Nivat.LE2.dot nℓ (z + (w - a)) →
        z + (w - a) ∈ Nivat.LE2.halfStrip B vl)
    (hKL : Nivat.ColleReg.chainFull B vl u' b₀ k ⊆
      Nivat.LE2.halfStrip B vl ∪
        (⋃ i : ℕ, (Nivat.ConeRegion.coneRegion B vl u' ∩
          {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)}))) :
    Nivat.Colle41.PeriodOn (Nivat.T e ξ) (Nivat.ColleReg.chainFull B vl u' b₀ k) (c • vl) :=
  hbase_of_cone_halfStrip hS ha hconv k hD
    (hwinL_cone_halfStrip_of_hstrict_of_geom hstrict hcone hstrip) hKL

/-! ## §9. 🔴 Verdict on `hKL`'s cover: `H_B(ℓ) ∪ ⋃ lines` does **not** exhaust `𝓡_{ι-1}` -/

/-- **The witness for §9.**  The lattice triangle with vertices `(2,0)`, `(2,2)`, `(0,2)`, cut
out by `x + y ≥ 2`, `x ≤ 2`, `y ≤ 2`.  Six lattice points.

The property that matters is that it **leans right as the level drops**: at its bottom level
`y = 0` it contains only `(2,0)`, while at its top level `y = 2` it reaches left to `(0,2)`.
Sweeping `(0,2)` straight down by `u'` therefore exits the half-strip, which at level `0` is
only `{(x,0) : x ≥ 2}`. -/
private def leanTri : Set (ℤ × ℤ) := {z | 2 ≤ z.1 + z.2 ∧ z.1 ≤ 2 ∧ z.2 ≤ 2}

private theorem mem_leanTri {z : ℤ × ℤ} :
    z ∈ leanTri ↔ 2 ≤ z.1 + z.2 ∧ z.1 ≤ 2 ∧ z.2 ≤ 2 := Iff.rfl

private theorem leanTri_finite : leanTri.Finite := by
  refine Set.Finite.subset ((Set.finite_Icc (0 : ℤ) 2).prod (Set.finite_Icc (0 : ℤ) 2)) ?_
  rintro z ⟨h1, h2, h3⟩
  exact ⟨Set.mem_Icc.mpr ⟨by omega, h2⟩, Set.mem_Icc.mpr ⟨by omega, h3⟩⟩

private theorem leanTri_latticeConvex : Nivat.IsLatticeConvexRegion leanTri := by
  refine ⟨{x : ℝ × ℝ | 2 ≤ x.1 + x.2 ∧ x.1 ≤ 2 ∧ x.2 ≤ 2}, ?_, ?_, ?_⟩
  · rintro x ⟨hx1, hx2, hx3⟩ y ⟨hy1, hy2, hy3⟩ α β hα hβ hαβ
    refine ⟨?_, ?_, ?_⟩
    · show (2 : ℝ) ≤ (α • x + β • y).1 + (α • x + β • y).2
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      nlinarith
    · show (α • x + β • y).1 ≤ (2 : ℝ)
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      nlinarith
    · show (α • x + β • y).2 ≤ (2 : ℝ)
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      nlinarith
  · have h1 : IsClosed {x : ℝ × ℝ | 2 ≤ x.1 + x.2} :=
      isClosed_le continuous_const (continuous_fst.add continuous_snd)
    have h2 : IsClosed {x : ℝ × ℝ | x.1 ≤ 2} := isClosed_le continuous_fst continuous_const
    have h3 : IsClosed {x : ℝ × ℝ | x.2 ≤ 2} := isClosed_le continuous_snd continuous_const
    exact h1.inter (h2.inter h3)
  · ext z
    simp only [Set.mem_preimage, Nivat.toReal]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨?_, ?_, ?_⟩
      · show (2 : ℝ) ≤ (z.1 : ℝ) + (z.2 : ℝ); exact_mod_cast h1
      · show (z.1 : ℝ) ≤ (2 : ℝ); exact_mod_cast h2
      · show (z.2 : ℝ) ≤ (2 : ℝ); exact_mod_cast h3
    · rintro ⟨h1, h2, h3⟩
      have g1 : (2 : ℝ) ≤ (z.1 : ℝ) + (z.2 : ℝ) := h1
      have g2 : (z.1 : ℝ) ≤ (2 : ℝ) := h2
      have g3 : (z.2 : ℝ) ≤ (2 : ℝ) := h3
      exact ⟨by exact_mod_cast g1, by exact_mod_cast g2, by exact_mod_cast g3⟩

private theorem leanTri_posArea : Nivat.LE2.PosArea leanTri :=
  ⟨((2 : ℤ), (0 : ℤ)), mem_leanTri.mpr ⟨by norm_num, by norm_num, by norm_num⟩,
   ((2 : ℤ), (2 : ℤ)), mem_leanTri.mpr ⟨by norm_num, by norm_num, by norm_num⟩,
   ((0 : ℤ), (2 : ℤ)), mem_leanTri.mpr ⟨by norm_num, by norm_num, by norm_num⟩,
   by norm_num [Nivat.det]⟩

/-- The uncovered point, isolated so that both §9 and §11 can cite the same computation.

`(0,0) = (0,2) + 0·(1,0) + 2·(0,-1)` is in the cone; it sits at level `0`, so it is on no line;
and `(0,0) = b + t·(1,0)` forces `b = (-t,0) ∉ leanTri`. -/
private theorem leanTri_cover_fails :
    ¬ (Nivat.ConeRegion.coneRegion leanTri ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (-1 : ℤ)) ⊆
        Nivat.LE2.halfStrip leanTri ((1 : ℤ), (0 : ℤ)) ∪
          (⋃ i : ℕ, Nivat.ConeRegion.coneRegion leanTri ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (-1 : ℤ)) ∩
            {y | Nivat.LE2.dot ((0 : ℤ), (1 : ℤ)) y = (0 : ℤ) - 1 - (i : ℤ)})) := by
  intro hsub
  have hp : ((0 : ℤ), (0 : ℤ)) ∈
      Nivat.ConeRegion.coneRegion leanTri ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (-1 : ℤ)) := by
    rw [Nivat.ConeRegion.mem_coneRegion_iff]
    refine ⟨((0 : ℤ), (2 : ℤ)),
      mem_leanTri.mpr ⟨by norm_num, by norm_num, by norm_num⟩, 0, 2, ?_⟩
    norm_num
  rcases hsub hp with hstrip | hlines
  · obtain ⟨b, hb, t, hbt⟩ := hstrip
    obtain ⟨h1, -, -⟩ := mem_leanTri.mp hb
    rw [Prod.ext_iff] at hbt
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      mul_one, mul_zero] at hbt
    obtain ⟨e1, e2⟩ := hbt
    omega
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hlines
    have hlev : Nivat.LE2.dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (0 : ℤ))
        = (0 : ℤ) - 1 - (i : ℤ) := hi.2
    simp only [Nivat.LE2.dot] at hlev
    omega

/-- **🔴 Verdict: the cover is false, and the witness is a genuine lattice-convex region of
positive area.**

原文：b3_colle2.txt:414, :784, :800.  `H_B(ℓ) := {g + t·v⃗_ℓ : g ∈ B}` (`:414`),
`𝓡_{ι-1} := {g + t·v⃗_{ℓ_{ι-1}} : g ∈ H_B(ℓ)}` (`:784`), `A_1 := 𝓡_{ι-1} ∩ l_1` with
`l_1 := ℓ_B^{(-)}` strictly below the band (`:800`).  The claim under test is that
`𝓡_{ι-1} = H_B(ℓ) ∪ ⋃_i A_i`, which is what `hKL` needs.

**It is false.**  Take `B` = the lattice triangle `leanTri` (vertices `(2,0)`, `(2,2)`,
`(0,2)`), `v⃗_ℓ = (1,0)`, `u' = (0,-1)`, `nℓ = (0,1)`, `cz = 0` (= `B`'s bottom level).  Then

    (0,0) = (0,2) + 0·v⃗_ℓ + 2·u'  ∈  𝓡_{ι-1}

sits at level `0 = cz`, so it is on **no** line `l_i` (those live at levels `≤ cz - 1`).  And it
is not in `H_B(ℓ)`: `(0,0) = b + t·(1,0)` forces `b = (-t, 0)` with `t ≥ 0`, whence
`b.1 + b.2 = -t ≤ 0 < 2`, so `b ∉ B`.

**All six hypotheses are discharged on the witness** (`PROTOCOL.md` §7, and the lesson of
`EnvTranslate.lean:119-132` where a "counterexample" asserted `Enveloped U T` for a `T` that was
not lattice-convex): `leanTri_finite`, nonemptiness at `(2,2)`, `leanTri_latticeConvex` (as the
`toReal`-preimage of a closed convex intersection of three half-planes), `leanTri_posArea`
(`det ((2,2)-(2,0)) ((0,2)-(2,0)) = 4`), `⟪nℓ,vl⟫ = 0`, `⟪nℓ,u'⟫ = -1`, and `cz = 0` a genuine
lower bound for `⟪nℓ,·⟫` on `B`.  This is **not** my withdrawn singleton `B`: it is
two-dimensional, tall, and wide.

**What fails, in one sentence.**  `H_B(ℓ)` sweeps only in `+v⃗_ℓ`, so at each level it is a
*right* ray starting where `B` starts at that level; a region that leans right as the level
drops has cone points that fall to the **left** of that ray while still inside the band.  The
obstruction is one-sidedness of the `v⃗_ℓ` sweep, not any choice of `cz` — moving `cz` up only
shrinks the line family, and moving it down leaves this point uncovered all the same.

⚠ **读法, 非内核事实 (for the consumer, the theorem itself is a kernel fact).**  Per the
dispatch: the follow-up is *not* to reshape the cover.  What this says is that `coneRegion`
(`= sweep (sweep B vl) u'`) is not interchangeable with Collé's `𝓡_{ι-1}` for covering
purposes, and the next question is what `(-ℓ, ℓ_{ι-1})`-region means at `:786` — in particular
whether `𝓡_{ι-1}` is meant to be a two-sided strip in `v⃗_ℓ`, for which this witness says
nothing.

## 🔵 补充 (2026-09-20)：原文审计关掉了「两侧带」这条出路，并**另外**排除了本见证

两件事，方向相反，都要记下来。

1. **审计判定：`t ∈ ℤ₊` 站得住，本反例打中的就是正确的陈述。**  `b3_colle2.txt:405` 定义
   `ℓ^{(-)}` 为「平行于 `ℓ`、离 `H(ℓ)` 最近、且 `H(ℓ) ∩ ℓ' = ∅` 的格线」，即**半平面之外**的
   第一条线；于是 `l₁ := ℓ_B^{(-)}` (`:796`) 在 `B` 的带**之下**，`cz` 取下界是对的，
   单侧扫掠也是对的。上一段那句「下一个问题是 `(-ℓ, ℓ_{ι-1})`-region 是不是两侧带」
   **已被审计否掉**，不要再沿它走。

2. **但本见证仍被 `:774` 独立排除。**  原文说生成集 `𝒮` 「has an edge parallel to `ℓ` and
   another one parallel to `−ℓ`」，经 `Enveloped.E_eq`（`LatticeEdges.lean:1657`）转给 `B`，
   即 `E B` 同时含 `nℓ` 与 `−nℓ`。`leanTri` 的底部是一个**顶点** `(2,0)` 而不是一条边，
   所以 `−nℓ = (0,-1) ∉ E leanTri`——见 §11 的内核记录
   `cover_witness_has_no_edge_parallel_to_neg_ell`。

**合起来的读法（非内核事实）**：本定理说「覆盖在裸的凸 + 正面积假设下为假」，
它**不**说覆盖在 Collé 的假设下为假。缺的那条假设已经有名字，见 §10 的 `hmono`。 -/
theorem not_coneRegion_subset_halfStrip_union_lines :
    ∃ (B : Set (ℤ × ℤ)) (vl u' nℓ : ℤ × ℤ) (cz : ℤ),
      Nivat.LE2.dot nℓ vl = 0 ∧ Nivat.LE2.dot nℓ u' = -1 ∧
      B.Finite ∧ B.Nonempty ∧ Nivat.IsLatticeConvexRegion B ∧ Nivat.LE2.PosArea B ∧
      (∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b) ∧
      ¬ (Nivat.ConeRegion.coneRegion B vl u' ⊆ Nivat.LE2.halfStrip B vl ∪
          (⋃ i : ℕ, Nivat.ConeRegion.coneRegion B vl u' ∩
            {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)})) := by
  refine ⟨leanTri, ((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (-1 : ℤ)), ((0 : ℤ), (1 : ℤ)), 0,
    by norm_num [Nivat.LE2.dot], by norm_num [Nivat.LE2.dot], leanTri_finite,
    ⟨((2 : ℤ), (2 : ℤ)), mem_leanTri.mpr ⟨by norm_num, by norm_num, by norm_num⟩⟩,
    leanTri_latticeConvex, leanTri_posArea, ?_, ?_⟩
  · intro b hb
    obtain ⟨h1, h2, h3⟩ := mem_leanTri.mp hb
    show (0 : ℤ) ≤ Nivat.LE2.dot ((0 : ℤ), (1 : ℤ)) b
    simp only [Nivat.LE2.dot]
    omega
  · exact leanTri_cover_fails

/-! ## §10. The cover is **equivalent** to one condition on `B` and `u'`: `hmono` -/

/-- `⟪n, b + t•u'⟫` expanded.  Helper for §10. -/
private theorem dot_step (n b u' : ℤ × ℤ) (t : ℤ) :
    Nivat.LE2.dot n (b + t • u') = Nivat.LE2.dot n b + t * Nivat.LE2.dot n u' := by
  simp only [Nivat.LE2.dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  ring

/-- **The cover's exact content: `hmono`.**

原文：b3_colle2.txt:405, :414, :784, :796.

The statement §9 refutes — that `𝓡_{ι-1}`'s part at or above `ℓ_B` is already `H_B(ℓ)` — is
**equivalent**, with no convexity and no finiteness, to a single condition on the pair `(B, u')`:

    hmono : ∀ b ∈ B, ∀ t : ℕ, cz ≤ ⟪nℓ,b⟫ - t → b + t•u' ∈ H_B(ℓ)

i.e. *dropping a base point of `B` by `u'` keeps it over `B` until it leaves the band.*

It is stated as an `↔` deliberately (`CLAUDE.md` hard rule 7): `hmono` is not a new hypothesis
we invented to rescue the route, it **is** the cover, restated so that its failure has a name.
§9's `leanTri` fails it at `b = (0,2)`, `t = 2`.

**量词对应原文**:
- `hperp : ⟪nℓ,vl⟫ = 0` ↔ the `l_i` are parallel to `ℓ` (Notation 3.3, `:406`; `:796`)
- `hstep : ⟪nℓ,u'⟫ = -1` ↔ `l_2 := l_1^{(-)}`, one `u'`-step per line (`:405`, `:802-804`)
- `cz` ↔ the level of `ℓ_B`; by `:405` the line `ℓ_B^{(-)}` lies strictly **outside** `H(ℓ_B)`,
  so `cz` is `B`'s bottom level and the lines start at `cz - 1`
- `b ∈ B`, `t : ℕ` ↔ the `g ∈ H_B(ℓ)`, `t ∈ ℤ_+` of `:784`
- conclusion `∈ H_B(ℓ)` ↔ "the knowledge of `T^u η` on `H_B(ℓ)` determines `T^u η` on `A_1`"
  (`:796`) — the only region the induction ever has in hand

There is no `B.Finite`, no `B.Nonempty` and no convexity here: the equivalence is pure
arithmetic in `nℓ`. -/
theorem coneRegion_inter_level_subset_halfStrip_iff_hmono
    {B : Set (ℤ × ℤ)} {vl u' nℓ : ℤ × ℤ} {cz : ℤ}
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hstep : Nivat.LE2.dot nℓ u' = -1) :
    (Nivat.ConeRegion.coneRegion B vl u' ∩ {z | cz ≤ Nivat.LE2.dot nℓ z}
       ⊆ Nivat.LE2.halfStrip B vl)
    ↔ (∀ b ∈ B, ∀ t : ℕ, cz ≤ Nivat.LE2.dot nℓ b - (t : ℤ) →
         b + (t : ℤ) • u' ∈ Nivat.LE2.halfStrip B vl) := by
  constructor
  · intro hsub b hb t hlev
    refine hsub ⟨?_, ?_⟩
    · rw [Nivat.ConeRegion.mem_coneRegion_iff]
      exact ⟨b, hb, 0, t, by simp⟩
    · show cz ≤ Nivat.LE2.dot nℓ (b + (t : ℤ) • u')
      rw [dot_step, hstep]
      omega
  · rintro hmono z ⟨hzc, hzlev⟩
    rw [Nivat.ConeRegion.mem_coneRegion_iff] at hzc
    obtain ⟨b, hb, s, t, rfl⟩ := hzc
    have hlev : cz ≤ Nivat.LE2.dot nℓ (b + (s : ℤ) • vl + (t : ℤ) • u') := hzlev
    rw [dot_cone_pt, hperp, hstep] at hlev
    obtain ⟨b', hb', t', hbt'⟩ := hmono b hb t (by omega)
    refine ⟨b', hb', t' + s, ?_⟩
    have hre : b + (s : ℤ) • vl + (t : ℤ) • u' = (b + (t : ℤ) • u') + (s : ℤ) • vl := by abel
    rw [hre, hbt']
    push_cast [add_smul]
    abel

/-- **The cover, from `hmono`.**  `𝓡_{ι-1} ⊆ H_B(ℓ) ∪ ⋃_i A_{i+1}`.

原文：b3_colle2.txt:796-804 — "proceeding this way" exhausts `𝓡_{ι-1}` line by line.  Above the
band this is §10's `↔`; below it, every cone point sits on exactly one line
`{⟪nℓ,·⟫ = cz - 1 - i}`, which is the `toNat` computation. -/
theorem coneRegion_subset_halfStrip_union_lines_of_hmono
    {B : Set (ℤ × ℤ)} {vl u' nℓ : ℤ × ℤ} {cz : ℤ}
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hstep : Nivat.LE2.dot nℓ u' = -1)
    (hmono : ∀ b ∈ B, ∀ t : ℕ, cz ≤ Nivat.LE2.dot nℓ b - (t : ℤ) →
      b + (t : ℤ) • u' ∈ Nivat.LE2.halfStrip B vl) :
    Nivat.ConeRegion.coneRegion B vl u' ⊆
      Nivat.LE2.halfStrip B vl ∪
        (⋃ i : ℕ, Nivat.ConeRegion.coneRegion B vl u' ∩
          {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)}) := by
  intro z hz
  by_cases hup : cz ≤ Nivat.LE2.dot nℓ z
  · exact Or.inl
      ((coneRegion_inter_level_subset_halfStrip_iff_hmono hperp hstep).mpr hmono ⟨hz, hup⟩)
  · push Not at hup
    refine Or.inr (Set.mem_iUnion.mpr
      ⟨(cz - 1 - Nivat.LE2.dot nℓ z).toNat, hz, ?_⟩)
    show Nivat.LE2.dot nℓ z = cz - 1 - ((cz - 1 - Nivat.LE2.dot nℓ z).toNat : ℤ)
    omega

/-- **`hbase` with `hKL` replaced by `hmono` plus one containment.**

This is `hbase_of_cone_halfStrip_of_geom` (`:749`) wired to §10.  What changed:

| binder | before | after |
|---|---|---|
| `hKL` | `chainFull ⊆ H_B(ℓ) ∪ ⋃ lines` | split into `hchain` and `hmono` |
| `hmono` | — | §10; being proved by another lane as `exists_shear_hmono` |
| `hchain` | — | `chainFull B vl u' b₀ k ⊆ 𝓡_{ι-1}` |

⚠ **`hchain` is not free, and I am not claiming it is** (`PROTOCOL.md` §15, 读法).
`chainFull` is a cut of `wedgeFull`, which sweeps `±vl` (`ConeHbase.lean:27-32`), whereas
`coneRegion` sweeps `+vl` only; `Nivat.ConeHbase.not_chainFull_subset_coneRegion`
(`ConeHbase.lean`) is the kernel witness that the containment fails for some `B, vl, u', b₀, k`.
So this theorem moves `hKL` from "one opaque covering" to "`hmono` (source-aligned, being
proved) **and** a `chainFull`-vs-`coneRegion` shape mismatch that is a separate, named debt".

`u'` remains a free variable constrained by nothing, so the shear `u' ↦ u' - K • vl` of
`WedgeAssemble.nonempty_wedgeResidualR_of_hbase_at_shear` survives. -/
theorem hbase_of_cone_halfStrip_of_hmono {ξ : Config ℤ} {e : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    {B : Set (ℤ × ℤ)} {vl u' b₀ nℓ : ℤ × ℤ} {c cz : ℤ}
    -- 🔴 2026-09-21 集成者：`GeneratesAt ξ S a` 换成原文 `:786`+`:790`+`:792` 的捆绑形状。
    -- 原文从未断言 `𝒮_{φ_ι}` 生成 `ξ` 本身，只断言它在 `ZMod p` 里生成差 `η − η̄_{ι₀}`。
    (hS : Nivat.SweepLines.ReducedGeneratesAt ξ S a (c • vl))
    (ha : a ∈ S) (hconv : Nivat.LatticeConvex (S.erase a)) (k : ℕ)
    (hD : ∀ z ∈ Nivat.LE2.halfStrip B vl,
      (Nivat.T e ξ) z = Nivat.T (c • vl) (Nivat.T e ξ) z)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hstep : Nivat.LE2.dot nℓ u' = -1)
    (hstrict : ∀ z ∈ S.erase a, Nivat.LE2.dot nℓ a < Nivat.LE2.dot nℓ z)
    (hcone : ∀ w ∈ Nivat.ConeRegion.coneRegion B vl u', Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ S.erase a, Nivat.LE2.dot nℓ (z + (w - a)) < cz →
        z + (w - a) ∈ Nivat.ConeRegion.coneRegion B vl u')
    (hstrip : ∀ w ∈ Nivat.ConeRegion.coneRegion B vl u', Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ S.erase a, cz ≤ Nivat.LE2.dot nℓ (z + (w - a)) →
        z + (w - a) ∈ Nivat.LE2.halfStrip B vl)
    (hmono : ∀ b ∈ B, ∀ t : ℕ, cz ≤ Nivat.LE2.dot nℓ b - (t : ℤ) →
      b + (t : ℤ) • u' ∈ Nivat.LE2.halfStrip B vl)
    (hchain : Nivat.ColleReg.chainFull B vl u' b₀ k ⊆
      Nivat.ConeRegion.coneRegion B vl u') :
    Nivat.Colle41.PeriodOn (Nivat.T e ξ) (Nivat.ColleReg.chainFull B vl u' b₀ k) (c • vl) :=
  hbase_of_cone_halfStrip_of_geom hS ha hconv k hD hstrict hcone hstrip
    (hchain.trans (coneRegion_subset_halfStrip_union_lines_of_hmono hperp hstep hmono))

/-! ## §11. Confining §9: the witness has no edge parallel to `−ℓ`, so `:774` excludes it -/

/-- The `(0,-1)`-face of `leanTri` is the single point `(2,0)`. -/
private theorem leanTri_bottom (z : ℤ × ℤ) (hz : z ∈ leanTri)
    (hmin : ∀ y ∈ leanTri,
      Nivat.LE2.dot ((0 : ℤ), (-1 : ℤ)) y ≤ Nivat.LE2.dot ((0 : ℤ), (-1 : ℤ)) z) :
    z = ((2 : ℤ), (0 : ℤ)) := by
  obtain ⟨z1, z2⟩ := z
  obtain ⟨h1, h2, h3⟩ := mem_leanTri.mp hz
  have hcmp := hmin ((2 : ℤ), (0 : ℤ))
    (mem_leanTri.mpr ⟨by norm_num, by norm_num, by norm_num⟩)
  simp only [Nivat.LE2.dot] at hcmp
  simp only [Prod.mk.injEq]
  simp only at h1 h2 h3
  omega

/-- `−nℓ = (0,-1)` is **not** an edge normal of `leanTri`: its bottom is a vertex. -/
private theorem neg_not_mem_E_leanTri : ((0 : ℤ), (-1 : ℤ)) ∉ Nivat.LE2.E leanTri := by
  intro hmem
  obtain ⟨-, x, hx, y, hy, hxy⟩ := Nivat.LE2.mem_E_iff.mp hmem
  exact hxy ((leanTri_bottom x hx.1 hx.2).trans (leanTri_bottom y hy.1 hy.2).symm)

/-- `nℓ = (0,1)` **is** an edge normal of `leanTri`: its top edge carries `(0,2)` and `(1,2)`. -/
private theorem mem_E_leanTri_top : ((0 : ℤ), (1 : ℤ)) ∈ Nivat.LE2.E leanTri := by
  refine Nivat.LE2.mem_E_iff.mpr ⟨by decide, ⟨((0 : ℤ), (2 : ℤ)), ⟨?_, ?_⟩,
    ((1 : ℤ), (2 : ℤ)), ⟨?_, ?_⟩, by simp⟩⟩
  · exact mem_leanTri.mpr ⟨by norm_num, by norm_num, by norm_num⟩
  · intro y hy
    obtain ⟨-, -, h3⟩ := mem_leanTri.mp hy
    simp only [Nivat.LE2.dot]
    omega
  · exact mem_leanTri.mpr ⟨by norm_num, by norm_num, by norm_num⟩
  · intro y hy
    obtain ⟨-, -, h3⟩ := mem_leanTri.mp hy
    simp only [Nivat.LE2.dot]
    omega

/-- **§9's witness is excluded by `b3_colle2.txt:774`, independently of the singleton objection.**

原文：b3_colle2.txt:774 — the generating set `𝒮` "has an edge parallel to `ℓ` and another one
parallel to `−ℓ`".  Through `Nivat.LE2.Enveloped.E_eq` (`LatticeEdges.lean:1657`) an
`E(𝒮_φ)`-enveloped `B` has `E B = E ↑𝒮_φ`, so **both** `nℓ` and `−nℓ` must lie in `E B`.

`leanTri` has `nℓ = (0,1) ∈ E` (top edge `(0,2)—(2,2)`) but `−nℓ = (0,-1) ∉ E`: its bottom is
the single vertex `(2,0)`.  So `not_coneRegion_subset_halfStrip_union_lines` (`:913`) refutes the
cover only over a `B` that Collé's setting never produces.

⚠ **This does not repair the cover** (`PROTOCOL.md` §15, 读法 for the consumer).  It says the
refutation is confined, not that the cover is true; what makes it true is exactly §10's `hmono`,
and `hmono` still needs a producer.  The value of recording this is that the next round does not
re-derive `leanTri` and re-conclude that the cone geometry is dead.

The two edge facts and the refutation are bundled into one statement on purpose: the point is
that a *single* `B` has all three properties. -/
theorem cover_witness_has_no_edge_parallel_to_neg_ell :
    ∃ (B : Set (ℤ × ℤ)) (vl u' nℓ : ℤ × ℤ) (cz : ℤ),
      Nivat.LE2.dot nℓ vl = 0 ∧ Nivat.LE2.dot nℓ u' = -1 ∧
      B.Finite ∧ B.Nonempty ∧ Nivat.IsLatticeConvexRegion B ∧ Nivat.LE2.PosArea B ∧
      (∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b) ∧
      nℓ ∈ Nivat.LE2.E B ∧ (-nℓ) ∉ Nivat.LE2.E B ∧
      ¬ (Nivat.ConeRegion.coneRegion B vl u' ⊆ Nivat.LE2.halfStrip B vl ∪
          (⋃ i : ℕ, Nivat.ConeRegion.coneRegion B vl u' ∩
            {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)})) := by
  refine ⟨leanTri, ((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (-1 : ℤ)), ((0 : ℤ), (1 : ℤ)), 0,
    by norm_num [Nivat.LE2.dot], by norm_num [Nivat.LE2.dot], leanTri_finite,
    ⟨((2 : ℤ), (2 : ℤ)), mem_leanTri.mpr ⟨by norm_num, by norm_num, by norm_num⟩⟩,
    leanTri_latticeConvex, leanTri_posArea, ?_, mem_E_leanTri_top, ?_, leanTri_cover_fails⟩
  · intro b hb
    obtain ⟨h1, h2, h3⟩ := mem_leanTri.mp hb
    show (0 : ℤ) ≤ Nivat.LE2.dot ((0 : ℤ), (1 : ℤ)) b
    simp only [Nivat.LE2.dot]
    omega
  · have hneg : (-((0 : ℤ), (1 : ℤ)) : ℤ × ℤ) = ((0 : ℤ), (-1 : ℤ)) := by
      simp
    rw [hneg]
    exact neg_not_mem_E_leanTri

/-! ## §12. `hchain` discharged by the `b₀`-argmax hypothesis, at the shifted base -/

/-- **`hbase` with `hchain` replaced by `b₀`-argmax — the debt of §10 paid.**

`hbase_of_cone_halfStrip_of_hmono` (`:1038`) carries a binder I flagged as a debt:

    hchain : ColleReg.chainFull B vl u' b₀ k ⊆ ConeRegion.coneRegion B vl u'

which `Nivat.ConeHbase.not_chainFull_subset_coneRegion` refutes in general (`chainFull` is a
cut of `wedgeFull`, which sweeps `±vl`; `coneRegion` sweeps `+vl` only).  The repair is
`Nivat.LE2.chainFull_subset_coneRegion_of_argmax_general` (`LineIndex.lean:366`): when `b₀` is
the **argmax** of `⟪expNormal u' vl, ·⟫` on `B`, the cut `⟪e,·⟫ ≥ ⟪e,b₀⟫ − k` forces the
`vl`-coefficient `s ≥ −k`, killing the `−vl` half up to `k` steps.

🔴 **The base shifts, and that is not papered over.**  `s ≥ −k` is *not* `s ≥ 0`, so the
containment does **not** land in `coneRegion B vl u'`; it lands in
`coneRegion (shift (-(k•vl)) B) vl u'`, rewriting `b + s•vl = (b − k•vl) + (s+k)•vl`.
`LineIndex.lean:351-360` records that the unshifted version is false for `k ≥ 1`.
Consequently **every** geometric binder here (`hD`, `hcone`, `hstrip`, `hmono`) is stated at
the shifted base `shift (-((k:ℤ)•vl)) B`, while the conclusion's `chainFull B vl u' b₀ k`
keeps the original `B`.  At `k = 0` the shift is the identity and this collapses to
`hbase_of_cone_halfStrip_of_hmono` minus `hchain`.

原文：b3_colle2.txt:780 (the construction of `𝓡_{ι-1}` from `H_B(ℓ)`), `:792-804` (the
line-by-line induction).  量词对应：`hb₀max` ↔ the choice of the outward extreme point at
`:780`; `k` ↔ the induction index `ι` of `:804`; the shift `−k•vl` has **no** counterpart in
the source — it is bookkeeping forced by our `chainFull`/`coneRegion` encodings, not a
strengthening of any hypothesis (it *weakens* nothing: it is a consequence, not an assumption).

**Consumer:** the same one as `:1038` — `WedgeAssemble.nonempty_wedgeResidualR_of_hbase_at_shear`
→ `ColleReg.wedgeResidualR_of_cone_hmono_at_shear` in `RegionSteps.lean`, discharging
`exists_wedgeResidualR`.  `hbase_of_cone_halfStrip_of_hmono` is **kept unchanged** beside this
one so that the existing wiring keeps compiling. -/
theorem hbase_of_cone_halfStrip_of_hmono_of_argmax {ξ : Config ℤ} {e : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    {B : Set (ℤ × ℤ)} {vl u' b₀ nℓ : ℤ × ℤ} {c cz : ℤ}
    -- 🔴 2026-09-21 集成者：`GeneratesAt ξ S a` 换成原文 `:786`+`:790`+`:792` 的捆绑形状。
    -- 原文从未断言 `𝒮_{φ_ι}` 生成 `ξ` 本身，只断言它在 `ZMod p` 里生成差 `η − η̄_{ι₀}`。
    (hS : Nivat.SweepLines.ReducedGeneratesAt ξ S a (c • vl))
    (ha : a ∈ S) (hconv : Nivat.LatticeConvex (S.erase a)) (k : ℕ)
    (hunimod : Nivat.det u' vl = 1 ∨ Nivat.det u' vl = -1)
    (hb₀max : ∀ b ∈ B, Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) b ≤
      Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) b₀)
    (hD : ∀ z ∈ Nivat.LE2.halfStrip (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl,
      (Nivat.T e ξ) z = Nivat.T (c • vl) (Nivat.T e ξ) z)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hstep : Nivat.LE2.dot nℓ u' = -1)
    (hstrict : ∀ z ∈ S.erase a, Nivat.LE2.dot nℓ a < Nivat.LE2.dot nℓ z)
    (hcone : ∀ w ∈ Nivat.ConeRegion.coneRegion (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl u',
      Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ S.erase a, Nivat.LE2.dot nℓ (z + (w - a)) < cz →
        z + (w - a) ∈
          Nivat.ConeRegion.coneRegion (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl u')
    (hstrip : ∀ w ∈ Nivat.ConeRegion.coneRegion (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl u',
      Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ S.erase a, cz ≤ Nivat.LE2.dot nℓ (z + (w - a)) →
        z + (w - a) ∈ Nivat.LE2.halfStrip (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl)
    (hmono : ∀ b ∈ Nivat.LE2.shift (-((k : ℤ) • vl)) B, ∀ t : ℕ,
      cz ≤ Nivat.LE2.dot nℓ b - (t : ℤ) →
        b + (t : ℤ) • u' ∈
          Nivat.LE2.halfStrip (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl) :
    Nivat.Colle41.PeriodOn (Nivat.T e ξ) (Nivat.ColleReg.chainFull B vl u' b₀ k) (c • vl) :=
  Nivat.SweepLines.hbase_at_of_sweep_lines_reduced hS ha hconv k hD
    (fun i => Nivat.ConeRegion.coneRegion (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl u' ∩
      {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)})
    (hwinL_cone_halfStrip_of_hstrict_of_geom hstrict hcone hstrip)
    (Nivat.LE2.chainFull_subset_halfStrip_union_lines_of_hmono k hunimod hperp hstep
      hb₀max hmono)

/-- **The argmax hypothesis of §12 is free for finite nonempty `B`.**

`hb₀max` is not an extra assumption on `B`: `Nivat.LE2.exists_argmax_expNormal`
(`LineIndex.lean:282`) produces the argmax from finiteness and nonemptiness alone.  This
restates it in the exact shape §12 consumes, so a caller who owns `B.Finite` and `B.Nonempty`
owes nothing for that binder — it only has to *choose* `b₀`, which is what
`chainFull B vl u' b₀ k` lets it do.

原文：b3_colle2.txt:780 — "`𝒮_{φ_ι}` is placed at an arbitrary point of `𝓡_{ι-1}`"; the
extreme point of `B` in the `expNormal u' vl` direction is the paper's base point. -/
theorem exists_argmax_base {B : Set (ℤ × ℤ)} (hfin : B.Finite) (hne : B.Nonempty)
    (u' vl : ℤ × ℤ) :
    ∃ b₀ ∈ B, ∀ b ∈ B, Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) b ≤
      Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) b₀ :=
  Nivat.LE2.exists_argmax_expNormal hfin hne u' vl

/-! ## §13. Why `hcone` is free and `hstrip` is not, and what `hstrip` forces on `B` -/

/-- `halfStrip` preserves the `nℓ`-level: every point of `H_B(ℓ)` sits on a level `B` occupies.

This is `⟪nℓ,vl⟫ = 0` and nothing else.  原文：b3_colle2.txt:414 (Definition 3.4) — the
half-strip is swept by `v⃗_ℓ`, which lies *in* the line `ℓ`, so sweeping never changes level. -/
private theorem dot_mem_halfStrip {B : Set (ℤ × ℤ)} {vl nℓ : ℤ × ℤ}
    (hperp : Nivat.LE2.dot nℓ vl = 0) {x : ℤ × ℤ}
    (hx : x ∈ Nivat.LE2.halfStrip B vl) :
    ∃ b ∈ B, Nivat.LE2.dot nℓ x = Nivat.LE2.dot nℓ b := by
  obtain ⟨b, hb, t, rfl⟩ := hx
  refine ⟨b, hb, ?_⟩
  rw [dot_step, hperp]
  ring

/-- **Half of the asymmetry: the cone absorbs steps along `u'`.**

`coneRegion B vl u' = {b + s•vl + t•u' : b ∈ B, s t : ℕ}` has a free `ℕ`-coefficient on `u'`,
so adding any `t•u'` is absorbed by incrementing it.  This is why `hcone`'s conclusion costs
nothing once the `vl`-coordinate is right: the level discrepancy created by translating the
seed down is simply added to `t`.

原文：b3_colle2.txt:784 — `𝓡_{ι-1} := {g + t·v⃗_{ℓ_{ι-1}} : g ∈ H_B(ℓ), t ∈ ℤ_+}`; the
`t ∈ ℤ_+` is the free coefficient. -/
theorem coneRegion_add_natSmul_step {B : Set (ℤ × ℤ)} {vl u' x : ℤ × ℤ}
    (hx : x ∈ Nivat.ConeRegion.coneRegion B vl u') (r : ℕ) :
    x + (r : ℤ) • u' ∈ Nivat.ConeRegion.coneRegion B vl u' := by
  rw [Nivat.ConeRegion.mem_coneRegion_iff] at hx ⊢
  obtain ⟨b, hb, s, t, rfl⟩ := hx
  refine ⟨b, hb, s, t + r, ?_⟩
  push_cast [add_smul]
  abel

/-- **The other half: the half-strip never absorbs a single step along `u'`.**

For *every* finite nonempty `B` — no convexity, no envelopedness, no edge condition — there is
a point of `H_B(ℓ)` that leaves `H_B(ℓ)` after one `u'`-step: take the level-minimal point of
`B`.  Sweeping by `vl` cannot lower a level (`dot_mem_halfStrip`), while `u'` lowers it by one,
so the result sits below every level `B` occupies.

**This is the answer to "why is `hcone` free and `hstrip` not".**  The two binders are the two
branches of one case split, with identical hypotheses; they differ only in the target.  The
cone's `u'`-coefficient is an unconstrained `ℕ` (`coneRegion_add_natSmul_step`), so it swallows
the level drop the translation creates.  The half-strip's is pinned to `0` — `H_B(ℓ)` meets
exactly the levels of `B` — so the drop must be paid for by `B` actually *having* a point on the
target level.  That is a condition on `B`, and `occupancy_of_hstrip` below extracts it.

原文：b3_colle2.txt:414 vs `:784`.  The source's own asymmetry: `H_B(ℓ)` is swept by `v⃗_ℓ`
alone, `𝓡_{ι-1}` by `v⃗_ℓ` and then `v⃗_{ℓ_{ι-1}}`. -/
theorem exists_mem_halfStrip_step_not_mem {B : Set (ℤ × ℤ)} {vl u' nℓ : ℤ × ℤ}
    (hfin : B.Finite) (hne : B.Nonempty)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hstep : Nivat.LE2.dot nℓ u' = -1) :
    ∃ x ∈ Nivat.LE2.halfStrip B vl, x + u' ∉ Nivat.LE2.halfStrip B vl := by
  obtain ⟨v, hv, heq⟩ := Nivat.LE2.exists_suppVal_eq hfin hne (-nℓ)
  refine ⟨v, Nivat.LE2.subset_halfStrip B vl hv, ?_⟩
  intro hmem
  obtain ⟨b, hb, hlev⟩ := dot_mem_halfStrip hperp hmem
  have hvu : Nivat.LE2.dot nℓ (v + u')
      = Nivat.LE2.dot nℓ v + Nivat.LE2.dot nℓ u' := Nivat.LE2.dot_add nℓ v u'
  have hbmin : Nivat.LE2.dot (-nℓ) b ≤ Nivat.LE2.suppVal B (-nℓ) :=
    Nivat.LE2.le_suppVal hfin hne hb
  rw [Nivat.LE2.dot_neg_left] at hbmin heq
  omega

/-- **What `hstrip` forces on `B`: it must occupy every level the seed reaches down to.**

原文：b3_colle2.txt:796-798.  The *reason* sentence in Figure 10's caption is
"Since `Ŝ_{φ_ι}` is an `η − η̄_{ι₀}`-generating set, then the knowledge of `T^u η` on `H_B(ℓ)`
determines uniquely `T^u η` on `A₁`" — and the premise that lets the translated seed sit with
its non-apex points inside `H_B(ℓ)` is `:777`, "Let `B ⊂ ℤ²` be an `E(𝒮_φ)`-**enveloped** set"
(Definition 3.2, `:402`).  **`hstrip` as stated carries no envelopedness**, and this theorem
measures exactly what that omission costs: the cheapest consequence of `hstrip` is that for a
seed point `z` hanging `d := ⟪nℓ, z − a⟫` levels above the apex, `B` must have a lattice point
on each of the `d` levels `cz, cz+1, …, cz+d−1`.

**量词对应**: `z ∈ S.erase a` ↔ the non-apex points of `𝒮_{φ_ι}` (`:794`); `j < d` ↔ the lines
`l₁, l₂, …` descending from `ℓ_B^{(-)}` (`:796`, `:802`), one per level the seed straddles;
`g ∈ B` ↔ the point of `B` whose `H_B(ℓ)`-ray receives the translate (`:414`).

⚠ **Direction matters, and it is the safe one.**  This *derives* a condition from `hstrip`, so
having fewer hypotheses than `:777` makes the statement **stronger**, not weaker — hard rule 10's
"比原文弱 = 白烧算力" governs refutations, where a dropped premise makes the counterexample
uninformative.  Here nothing is refuted: the conclusion holds a fortiori for enveloped `B`.

🔵 **Shear-uniform for free.**  `⟪nℓ, u' − K•vl⟫ = ⟪nℓ,u'⟫ − K·⟪nℓ,vl⟫ = -1` under `hperp`, so
every shear `u' ↦ u' − K•vl` satisfies `hstep` and is already an instance of this theorem.  A
level `B` fails to occupy therefore defeats `hstrip` at **every** `K` at once — the same
shear-invariance Wbox records for `hmono` in `EnvFit.occupancy_of_hmono`.

**Consumer:** `RegionSteps.lean:2836`, binder `hstrip`, via
`hbase_of_cone_halfStrip_of_hmono_of_argmax` (`:1170`). -/
theorem occupancy_of_hstrip {B : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    {vl u' nℓ : ℤ × ℤ} {cz : ℤ}
    (hne : B.Nonempty)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hstep : Nivat.LE2.dot nℓ u' = -1)
    (hcz : ∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b)
    (hstrip : ∀ w ∈ Nivat.ConeRegion.coneRegion B vl u', Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ S.erase a, cz ≤ Nivat.LE2.dot nℓ (z + (w - a)) →
        z + (w - a) ∈ Nivat.LE2.halfStrip B vl) :
    ∀ z ∈ S.erase a, ∀ j : ℕ, (j : ℤ) < Nivat.LE2.dot nℓ (z - a) →
      ∃ g ∈ B, Nivat.LE2.dot nℓ g = cz + (j : ℤ) := by
  intro z hz j hj
  obtain ⟨b₀, hb₀⟩ := hne
  have hd : Nivat.LE2.dot nℓ (z - a)
      = Nivat.LE2.dot nℓ z - Nivat.LE2.dot nℓ a := Nivat.LE2.dot_sub nℓ z a
  have hb₀cz : cz ≤ Nivat.LE2.dot nℓ b₀ := hcz b₀ hb₀
  -- the cone point one seed-drop below the target level
  set t : ℕ :=
    (Nivat.LE2.dot nℓ b₀ - (cz + (j : ℤ) - Nivat.LE2.dot nℓ (z - a))).toNat with htdef
  have htval : (t : ℤ)
      = Nivat.LE2.dot nℓ b₀ - (cz + (j : ℤ) - Nivat.LE2.dot nℓ (z - a)) := by
    rw [htdef]; omega
  set w : ℤ × ℤ := b₀ + (0 : ℤ) • vl + (t : ℤ) • u' with hwdef
  have hwcone : w ∈ Nivat.ConeRegion.coneRegion B vl u' := by
    rw [hwdef, Nivat.ConeRegion.mem_coneRegion_iff]
    exact ⟨b₀, hb₀, 0, t, by push_cast; ring_nf⟩
  have hwlevel : Nivat.LE2.dot nℓ w = Nivat.LE2.dot nℓ b₀ - (t : ℤ) := by
    rw [hwdef, dot_cone_pt, hperp, hstep]
    ring
  have hwlow : Nivat.LE2.dot nℓ w < cz := by omega
  have htrans : Nivat.LE2.dot nℓ (z + (w - a))
      = Nivat.LE2.dot nℓ z + Nivat.LE2.dot nℓ w - Nivat.LE2.dot nℓ a :=
    dot_translate_eq nℓ z w a
  have hhi : cz ≤ Nivat.LE2.dot nℓ (z + (w - a)) := by omega
  obtain ⟨g, hg, hglev⟩ := dot_mem_halfStrip hperp (hstrip w hwcone hwlow z hz hhi)
  exact ⟨g, hg, by omega⟩

/-! ## §14. `hstrip` at `K = 0`: its exact content, and why occupancy alone is not it -/

/-- `⟪n, c•x⟫ = c·⟪n,x⟫`.  Helper for §14. -/
private theorem dot_zsmul_right (n x : ℤ × ℤ) (c : ℤ) :
    Nivat.LE2.dot n (c • x) = c * Nivat.LE2.dot n x := by
  simp only [Nivat.LE2.dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **The `u'`-coordinate is minus the level.**

`basis_expansion` (`HbaseBridge.lean:763`) writes every `w` as
`⟪expNormal vl u', w⟫ • u' + ⟪expNormal u' vl, w⟫ • vl`.  Pairing that with `nℓ` and using
`hperp`/`hstep` kills the `vl` term and turns the `u'` term into `-⟪nℓ,w⟫`.  So in the
`(u', vl)` basis the coordinates of a point are exactly *(minus the level, `μ`)*, which is why
the whole of §14 is `(nℓ, μ)` arithmetic with no geometry. -/
private theorem dot_nu_eq_neg_level {vl u' nℓ : ℤ × ℤ}
    (hunimod : Nivat.det u' vl = 1 ∨ Nivat.det u' vl = -1)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hstep : Nivat.LE2.dot nℓ u' = -1) (w : ℤ × ℤ) :
    Nivat.LE2.dot (Nivat.ColleReg.expNormal vl u') w = - Nivat.LE2.dot nℓ w := by
  have hbasis := Nivat.HbaseBridge.basis_expansion hunimod w
  have h : Nivat.LE2.dot nℓ
      ((Nivat.LE2.dot (Nivat.ColleReg.expNormal vl u') w) • u'
        + (Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) w) • vl)
      = Nivat.LE2.dot nℓ w := by rw [hbasis]
  rw [Nivat.LE2.dot_add, dot_zsmul_right, dot_zsmul_right, hperp, hstep] at h
  linarith

/-- Two points on the same `nℓ`-level differ by a `vl`-multiple, and `μ` counts the multiple. -/
private theorem eq_add_zsmul_vl_of_level_eq {vl u' nℓ : ℤ × ℤ}
    (hunimod : Nivat.det u' vl = 1 ∨ Nivat.det u' vl = -1)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hstep : Nivat.LE2.dot nℓ u' = -1) {x b : ℤ × ℤ}
    (hlev : Nivat.LE2.dot nℓ b = Nivat.LE2.dot nℓ x) :
    x = b + (Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) x
              - Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) b) • vl := by
  have hbasis := Nivat.HbaseBridge.basis_expansion hunimod (x - b)
  have hnu : Nivat.LE2.dot (Nivat.ColleReg.expNormal vl u') (x - b) = 0 := by
    rw [dot_nu_eq_neg_level hunimod hperp hstep, Nivat.LE2.dot_sub]
    omega
  have hmu : Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) (x - b)
      = Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) x
        - Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) b := Nivat.LE2.dot_sub _ _ _
  rw [hnu, hmu, zero_smul, zero_add] at hbasis
  rw [hbasis]
  abel

/-- **The `(level, μ)` criterion for `H_B(ℓ)`.**

原文：b3_colle2.txt:414 (Definition 3.4).  `H_B(ℓ) = {g + t·v⃗_ℓ : g ∈ B, t ∈ ℤ_+}` sweeps `B`
by `v⃗_ℓ` only, so in the `(u', vl)` basis its membership test splits into exactly two clauses:

* **level**: `⟪nℓ,·⟫` is unchanged by the sweep (`hperp`), so `x` must sit on a level `B` occupies;
* **`μ`**: `μ := expNormal u' vl` has `⟪μ,vl⟫ = 1`, so the sweep only *increases* `μ`, and `x`
  must sit at or beyond the `μ` of some point of `B` on that level.

**量词对应原文**: `b ∈ B` ↔ the `g ∈ B` of `:414`; `t ∈ ℤ_+` ↔ the `ℕ`-coefficient, recovered
here as `μ x - μ b` — that recovery is what makes this an `↔` and not just a `→`.

`hunimod` is used only for `←`: `(u', vl)` must be a **basis** of `ℤ²`, or the two coordinates
do not determine the point. -/
theorem mem_halfStrip_iff_level_and_mu {B : Set (ℤ × ℤ)} {vl u' nℓ : ℤ × ℤ}
    (hunimod : Nivat.det u' vl = 1 ∨ Nivat.det u' vl = -1)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hstep : Nivat.LE2.dot nℓ u' = -1) (x : ℤ × ℤ) :
    x ∈ Nivat.LE2.halfStrip B vl ↔
      ∃ b ∈ B, Nivat.LE2.dot nℓ b = Nivat.LE2.dot nℓ x ∧
        Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) b
          ≤ Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) x := by
  constructor
  · rintro ⟨b, hb, t, rfl⟩
    refine ⟨b, hb, ?_, ?_⟩
    · rw [dot_step, hperp]; ring
    · rw [dot_step, Nivat.ColleReg.dot_expNormal_vl hunimod]
      have ht : (0 : ℤ) ≤ (t : ℤ) := by omega
      omega
  · rintro ⟨b, hb, hlev, hmu⟩
    refine ⟨b, hb, (Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) x
      - Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) b).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega)]
    exact eq_add_zsmul_vl_of_level_eq hunimod hperp hstep hlev

/-- **The `mpr` half of `hstrip_iff_fit_window`, with no hypothesis on `B` at all.**

Isolated because it is the direction the chain consumes, and because it shows that the
level-floor hypothesis `hcz` of `hstrip_iff_fit_window` belongs to *necessity* only: producing `hstrip`
from the fit condition needs nothing of `B` beyond `hunimod`/`hperp`/`hstep`.

原文：b3_colle2.txt:414, :784, :794-798.  A cone point is `b + s·v⃗_ℓ + t·v⃗_{ℓ_{ι-1}}`; the
translate of `z` by `w - a` therefore sits at level `⟪nℓ,b⟫ - t + ⟪nℓ,z-a⟫` and at
`μ = μ b + s + μ (z-a)`, with `s ≥ 0`.  `hfit` at the level index `j` supplies the point of `B`
that the half-strip criterion `mem_halfStrip_iff_level_and_mu` asks for. -/
theorem hstrip_of_fit_window {B : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    {vl u' nℓ : ℤ × ℤ} {cz : ℤ}
    (hunimod : Nivat.det u' vl = 1 ∨ Nivat.det u' vl = -1)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hstep : Nivat.LE2.dot nℓ u' = -1)
    (hfit : ∀ b ∈ B, ∀ z ∈ S.erase a, ∀ j : ℕ, (j : ℤ) < Nivat.LE2.dot nℓ (z - a) →
        ∃ g ∈ B, Nivat.LE2.dot nℓ g = cz + (j : ℤ) ∧
          Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) g ≤
            Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) b
              + Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) (z - a)) :
    ∀ w ∈ Nivat.ConeRegion.coneRegion B vl u', Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ S.erase a, cz ≤ Nivat.LE2.dot nℓ (z + (w - a)) →
        z + (w - a) ∈ Nivat.LE2.halfStrip B vl := by
  intro w hw hwlow z hz hhi
  rw [Nivat.ConeRegion.mem_coneRegion_iff] at hw
  obtain ⟨b, hb, s, t, hweq⟩ := hw
  have hwlevel : Nivat.LE2.dot nℓ w = Nivat.LE2.dot nℓ b - (t : ℤ) := by
    rw [hweq, dot_cone_pt, hperp, hstep]; ring
  have hwmu : Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) w
      = Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) b + (s : ℤ) := by
    rw [hweq, dot_cone_pt, Nivat.ColleReg.dot_expNormal_vl hunimod,
      Nivat.ColleReg.dot_expNormal_u']
    ring
  have hd : Nivat.LE2.dot nℓ (z - a)
      = Nivat.LE2.dot nℓ z - Nivat.LE2.dot nℓ a := Nivat.LE2.dot_sub nℓ z a
  have htrans : Nivat.LE2.dot nℓ (z + (w - a))
      = Nivat.LE2.dot nℓ z + Nivat.LE2.dot nℓ w - Nivat.LE2.dot nℓ a :=
    dot_translate_eq nℓ z w a
  set j : ℕ := (Nivat.LE2.dot nℓ (z + (w - a)) - cz).toNat with hjdef
  have hjval : (j : ℤ) = Nivat.LE2.dot nℓ (z + (w - a)) - cz := by
    rw [hjdef]; omega
  obtain ⟨g, hg, hglev, hgmu⟩ := hfit b hb z hz j (by omega)
  rw [mem_halfStrip_iff_level_and_mu hunimod hperp hstep]
  have htransmu : Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) (z + (w - a))
      = Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) z
        + Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) w
        - Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) a :=
    dot_translate_eq _ z w a
  have hmuza : Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) (z - a)
      = Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) z
        - Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) a := Nivat.LE2.dot_sub _ _ _
  have hs : (0 : ℤ) ≤ (s : ℤ) := by omega
  exact ⟨g, hg, by omega, by omega⟩

/-- **🔑 `hstrip` is *equivalent* to one condition on `(B, S, a)`, at the untilted `u'`.**

原文：b3_colle2.txt:777, :794-798.  This is for `hstrip` what
`coneRegion_inter_level_subset_halfStrip_iff_hmono` (`:968`) is for `hmono`: an `↔`, so the
right-hand side is not a hypothesis invented to rescue the route — it **is** `hstrip`, restated
so that what it asks of `B` has a name.  Per `CLAUDE.md` hard rule 7, each quantifier is traced:

- `b ∈ B`, `z ∈ S.erase a` ↔ the `g ∈ B` of `:414` and the non-apex points of `Ŝ_{φ_ι}` (`:794`);
- `j < ⟪nℓ, z-a⟫` ↔ the lines `l₁, l₂, …` of `:796`/`:802` that the translated seed straddles,
  one per level between `ℓ_B^{(-)}` and the seed's own top;
- `∃ g ∈ B, ⟪nℓ,g⟫ = cz + j` ↔ **occupancy**, the conclusion of `occupancy_of_hstrip` (`:1309`);
- `μ g ≤ μ b + μ (z - a)` ↔ the **`μ`-clause**: over the levels the seed straddles, `B`'s left
  boundary may not drift right by more than the seed's own point drifts right from its apex.

**Why the right-hand side is what it is.**  `𝓡_{ι-1}`'s `μ`-coordinate is bounded below by
`min_{b ∈ B} μ b`, because `⟪μ,u'⟫ = 0` (`dot_expNormal_u'`): sweeping by `u'` moves a point
*down* but never *left*.  So the cone does **not** reach arbitrarily far left below `cz`, and a
translate landing back at level `≥ cz` lands at `μ ≥ μ b + μ (z-a)`.  `hstrip` is then precisely
the demand that `B` already has a point that far left on the target level.

⚠ **Neither `hstrict` nor lattice convexity nor `hlean` is used**, and `hcz` is used only for
`→`; `mpr` asks nothing of `B` beyond `hunimod`/`hperp`/`hstep`.

**Consumer:** `RegionSteps.lean:2836`, binder `hstrip`, via
`hbase_of_cone_halfStrip_of_hmono_of_argmax` (`:1170`). -/
theorem hstrip_iff_fit_window {B : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    {vl u' nℓ : ℤ × ℤ} {cz : ℤ}
    (hunimod : Nivat.det u' vl = 1 ∨ Nivat.det u' vl = -1)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hstep : Nivat.LE2.dot nℓ u' = -1)
    (hcz : ∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b) :
    (∀ w ∈ Nivat.ConeRegion.coneRegion B vl u', Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ S.erase a, cz ≤ Nivat.LE2.dot nℓ (z + (w - a)) →
        z + (w - a) ∈ Nivat.LE2.halfStrip B vl)
    ↔ (∀ b ∈ B, ∀ z ∈ S.erase a, ∀ j : ℕ, (j : ℤ) < Nivat.LE2.dot nℓ (z - a) →
        ∃ g ∈ B, Nivat.LE2.dot nℓ g = cz + (j : ℤ) ∧
          Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) g ≤
            Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) b
              + Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) (z - a)) := by
  constructor
  · intro hstrip b hb z hz j hj
    have hbcz : cz ≤ Nivat.LE2.dot nℓ b := hcz b hb
    set t : ℕ :=
      (Nivat.LE2.dot nℓ b - cz - (j : ℤ) + Nivat.LE2.dot nℓ (z - a)).toNat with htdef
    have htval : (t : ℤ)
        = Nivat.LE2.dot nℓ b - cz - (j : ℤ) + Nivat.LE2.dot nℓ (z - a) := by
      rw [htdef]; omega
    set w : ℤ × ℤ := b + (0 : ℤ) • vl + (t : ℤ) • u' with hwdef
    have hwcone : w ∈ Nivat.ConeRegion.coneRegion B vl u' := by
      rw [hwdef, Nivat.ConeRegion.mem_coneRegion_iff]
      exact ⟨b, hb, 0, t, by push_cast; ring_nf⟩
    have hwlevel : Nivat.LE2.dot nℓ w = Nivat.LE2.dot nℓ b - (t : ℤ) := by
      rw [hwdef, dot_cone_pt, hperp, hstep]; ring
    have hwmu : Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) w
        = Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) b := by
      rw [hwdef, dot_cone_pt, Nivat.ColleReg.dot_expNormal_vl hunimod,
        Nivat.ColleReg.dot_expNormal_u']
      ring
    have hd : Nivat.LE2.dot nℓ (z - a)
        = Nivat.LE2.dot nℓ z - Nivat.LE2.dot nℓ a := Nivat.LE2.dot_sub nℓ z a
    have htrans : Nivat.LE2.dot nℓ (z + (w - a))
        = Nivat.LE2.dot nℓ z + Nivat.LE2.dot nℓ w - Nivat.LE2.dot nℓ a :=
      dot_translate_eq nℓ z w a
    have hwlow : Nivat.LE2.dot nℓ w < cz := by omega
    have hhi : cz ≤ Nivat.LE2.dot nℓ (z + (w - a)) := by omega
    have hmem := hstrip w hwcone hwlow z hz hhi
    rw [mem_halfStrip_iff_level_and_mu hunimod hperp hstep] at hmem
    obtain ⟨g, hg, hglev, hgmu⟩ := hmem
    have htransmu : Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) (z + (w - a))
        = Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) z
          + Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) w
          - Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) a :=
      dot_translate_eq _ z w a
    have hmuza : Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) (z - a)
        = Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) z
          - Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) a := Nivat.LE2.dot_sub _ _ _
    exact ⟨g, hg, by omega, by omega⟩
  · exact hstrip_of_fit_window hunimod hperp hstep

/-- **The producer of `hstrip` at `K = 0`: `hlean` plus `μ`-refined occupancy.**

原文：b3_colle2.txt:777 (`B` is `E(𝒮_φ)`-enveloped, Definition 3.2 at `:402`), :794-798.

`hlean` — "`B`'s `μ`-leftmost point sits at the `u'`-far level `cz`" — enters through its
**minimality half only**: `hbmin` says `μ bmin` is a lower bound for `μ` on `B`, which collapses
the `∀ b ∈ B` of `hstrip_iff_fit_window`'s right-hand side to the single instance at `bmin`.

⚠ **The level half `⟪nℓ, bmin⟫ = cz` is deliberately absent from this signature.**  It is not used
by the implication; what it does is make `hocc` *satisfiable* — by `occupancy_of_hstrip` (`:1309`)
the levels `cz … cz+d-1` must be occupied, and by `hmono`'s content (`:968`) `μ` is minimised at
the bottom of the band, so `μ bmin = m(cz)` is the strongest lower bound available.  An unused
binder here would only weaken the lemma (`PROTOCOL.md` §15).

⚠ **`hocc` is a named hypothesis with no producer yet**, per the dispatch.  Its first conjunct is
verbatim the conclusion of `occupancy_of_hstrip`, so that half is *necessary*, not an invention;
its second conjunct (the `μ`-clause) is the residue, and `not_hstrip_of_occupancy_without_mu`
below is the kernel witness that it cannot be dropped.  The premise that should produce it is
`:777`'s envelopedness, which `hstrip` as it reaches us does not carry.

**Consumer:** `RegionSteps.lean:2836`, binder `hstrip`, via
`hbase_of_cone_halfStrip_of_hmono_of_argmax` (`:1170`). -/
theorem hstrip_of_lean_of_occupancy {B : Set (ℤ × ℤ)} {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ}
    {vl u' nℓ bmin : ℤ × ℤ} {cz : ℤ}
    (hunimod : Nivat.det u' vl = 1 ∨ Nivat.det u' vl = -1)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hstep : Nivat.LE2.dot nℓ u' = -1)
    (hbmin : ∀ b ∈ B, Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) bmin
      ≤ Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) b)
    (hocc : ∀ z ∈ S.erase a, ∀ j : ℕ, (j : ℤ) < Nivat.LE2.dot nℓ (z - a) →
      ∃ g ∈ B, Nivat.LE2.dot nℓ g = cz + (j : ℤ) ∧
        Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) g ≤
          Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) bmin
            + Nivat.LE2.dot (Nivat.ColleReg.expNormal u' vl) (z - a)) :
    ∀ w ∈ Nivat.ConeRegion.coneRegion B vl u', Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ S.erase a, cz ≤ Nivat.LE2.dot nℓ (z + (w - a)) →
        z + (w - a) ∈ Nivat.LE2.halfStrip B vl :=
  hstrip_of_fit_window (S := S) (a := a) (cz := cz) hunimod hperp hstep
    (fun b hb z hz j hj => by
      obtain ⟨g, hg, hglev, hgmu⟩ := hocc z hz j hj
      exact ⟨g, hg, hglev, le_trans hgmu (by have := hbmin b hb; omega)⟩)

/-! ### §14b. The `μ`-clause is not removable -/

/-- **The witness for §14b.**  The lattice parallelogram with vertices `(0,0)`, `(1,0)`, `(2,1)`,
`(1,1)` — four lattice points, cut out by `0 ≤ y ≤ 1` and `y ≤ x ≤ y + 1`.

Unlike `leanTri` (`:780`), which leans *right as the level drops*, this one leans **left as the
level drops**: its `μ`-minimum `(0,0)` sits on its bottom level, so it satisfies `hlean`.  It
still defeats `hstrip`, because from level `0` to level `1` its left boundary moves right by one
while the seed vector `z - a = (0,2)` moves right by nothing. -/
private def slantPara : Set (ℤ × ℤ) :=
  {z | 0 ≤ z.2 ∧ z.2 ≤ 1 ∧ z.2 ≤ z.1 ∧ z.1 ≤ z.2 + 1}

private theorem mem_slantPara {z : ℤ × ℤ} :
    z ∈ slantPara ↔ 0 ≤ z.2 ∧ z.2 ≤ 1 ∧ z.2 ≤ z.1 ∧ z.1 ≤ z.2 + 1 := Iff.rfl

private theorem slantPara_finite : slantPara.Finite := by
  refine Set.Finite.subset ((Set.finite_Icc (0 : ℤ) 2).prod (Set.finite_Icc (0 : ℤ) 1)) ?_
  rintro z ⟨h1, h2, h3, h4⟩
  exact ⟨Set.mem_Icc.mpr ⟨by omega, by omega⟩, Set.mem_Icc.mpr ⟨h1, h2⟩⟩

private theorem slantPara_nonempty : slantPara.Nonempty :=
  ⟨((0 : ℤ), (0 : ℤ)), mem_slantPara.mpr ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

private theorem slantPara_latticeConvex : Nivat.IsLatticeConvexRegion slantPara := by
  refine ⟨{x : ℝ × ℝ | 0 ≤ x.2 ∧ x.2 ≤ 1 ∧ x.2 ≤ x.1 ∧ x.1 ≤ x.2 + 1}, ?_, ?_, ?_⟩
  · rintro x ⟨hx1, hx2, hx3, hx4⟩ y ⟨hy1, hy2, hy3, hy4⟩ α β hα hβ hαβ
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (0 : ℝ) ≤ (α • x + β • y).2
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      nlinarith
    · show (α • x + β • y).2 ≤ (1 : ℝ)
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      nlinarith
    · show (α • x + β • y).2 ≤ (α • x + β • y).1
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      nlinarith
    · show (α • x + β • y).1 ≤ (α • x + β • y).2 + 1
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      nlinarith
  · have h1 : IsClosed {x : ℝ × ℝ | 0 ≤ x.2} := isClosed_le continuous_const continuous_snd
    have h2 : IsClosed {x : ℝ × ℝ | x.2 ≤ 1} := isClosed_le continuous_snd continuous_const
    have h3 : IsClosed {x : ℝ × ℝ | x.2 ≤ x.1} := isClosed_le continuous_snd continuous_fst
    have h4 : IsClosed {x : ℝ × ℝ | x.1 ≤ x.2 + 1} :=
      isClosed_le continuous_fst (continuous_snd.add continuous_const)
    exact h1.inter (h2.inter (h3.inter h4))
  · ext z
    simp only [Set.mem_preimage, Nivat.toReal]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · show (0 : ℝ) ≤ (z.2 : ℝ); exact_mod_cast h1
      · show (z.2 : ℝ) ≤ (1 : ℝ); exact_mod_cast h2
      · show (z.2 : ℝ) ≤ (z.1 : ℝ); exact_mod_cast h3
      · show (z.1 : ℝ) ≤ (z.2 : ℝ) + (1 : ℝ); exact_mod_cast h4
    · rintro ⟨h1, h2, h3, h4⟩
      have g1 : (0 : ℝ) ≤ (z.2 : ℝ) := h1
      have g2 : (z.2 : ℝ) ≤ (1 : ℝ) := h2
      have g3 : (z.2 : ℝ) ≤ (z.1 : ℝ) := h3
      have g4 : (z.1 : ℝ) ≤ (z.2 : ℝ) + (1 : ℝ) := h4
      exact ⟨by exact_mod_cast g1, by exact_mod_cast g2, by exact_mod_cast g3,
        by exact_mod_cast g4⟩

private theorem slantPara_posArea : Nivat.LE2.PosArea slantPara :=
  ⟨((0 : ℤ), (0 : ℤ)), mem_slantPara.mpr ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩,
   ((1 : ℤ), (0 : ℤ)), mem_slantPara.mpr ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩,
   ((1 : ℤ), (1 : ℤ)), mem_slantPara.mpr ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩,
   by norm_num [Nivat.det]⟩

/-- The seed of §14b: apex `(0,0)`, one further point `(0,2)` two levels up and not one step
right.  `S.erase a` is a singleton, hence lattice-convex, and `hstrict` holds with `d = 2`. -/
private def wS : Finset (ℤ × ℤ) := {((0 : ℤ), (0 : ℤ)), ((0 : ℤ), (2 : ℤ))}

private theorem wS_erase : wS.erase ((0 : ℤ), (0 : ℤ)) = {((0 : ℤ), (2 : ℤ))} := by decide

private theorem mu_witness :
    Nivat.ColleReg.expNormal ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (0 : ℤ)) = ((1 : ℤ), (0 : ℤ)) := by
  simp only [Nivat.ColleReg.expNormal, Nivat.det, Prod.smul_mk, smul_eq_mul]
  norm_num

/-- **🔴 Occupancy alone does not give `hstrip`, even with `hlean` and a lattice-convex `B` of
positive area.**

原文：the hypothesis this witness is missing is **`b3_colle2.txt:777`** — "Let `B ⊂ ℤ²` be an
`E(𝒮_φ)`-**enveloped** set" (Definition 3.2, `:402`), which ties `B`'s edges to `𝒮_φ`'s and is
the only thing in Case 1 that compares the shape of `B` with the shape of the seed.  Everything
else Collé assumes of `B` in Case 1 holds here: `slantPara` is finite, non-empty, a lattice-convex
region of positive area, its bottom level is `cz = 0`, and its `μ`-minimum `(0,0)` sits **on**
that bottom level, so `hlean` holds in full.  Occupancy holds too: levels `0` and `1` — the two
the seed straddles — both carry a point of `B`.

What fails is only the `μ`-clause of `hstrip_iff_fit_window`: `B`'s left boundary climbs from `μ = 0` at
level `0` to `μ = 1` at level `1`, while `μ (z - a) = 0`.  The cone point `w = (0,-1)` then sends
`z = (0,2)` to `(0,1)`, which is at level `1 ≥ cz` and is **not** in `H_B(ℓ)`.

⚠ **Read this as a statement about our reduction, not about Collé** (`CLAUDE.md` hard rule 10).
`wS` is two points, so it is not a legal `𝒮_{φ_ι}`, and `slantPara` is not `E(wS)`-enveloped; the
witness therefore says nothing about whether Collé's Claim 4.6 is true.  What it does say is
exactly one thing: **the `μ`-clause in `hstrip_of_lean_of_occupancy`'s `hocc` cannot be deleted.**
A lane that produces occupancy alone has not produced `hstrip`, at `K = 0` or at any other `K`. -/
theorem not_hstrip_of_occupancy_without_mu :
    Nivat.det ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (0 : ℤ)) = 1 ∧
    Nivat.LE2.dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) = 0 ∧
    Nivat.LE2.dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) = -1 ∧
    slantPara.Finite ∧ slantPara.Nonempty ∧
    Nivat.IsLatticeConvexRegion slantPara ∧ Nivat.LE2.PosArea slantPara ∧
    ((0 : ℤ), (0 : ℤ)) ∈ wS ∧
    Nivat.LatticeConvex (wS.erase ((0 : ℤ), (0 : ℤ))) ∧
    (∀ z ∈ wS.erase ((0 : ℤ), (0 : ℤ)),
      Nivat.LE2.dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (0 : ℤ))
        < Nivat.LE2.dot ((0 : ℤ), (1 : ℤ)) z) ∧
    (∀ b ∈ slantPara, (0 : ℤ) ≤ Nivat.LE2.dot ((0 : ℤ), (1 : ℤ)) b) ∧
    ((0 : ℤ), (0 : ℤ)) ∈ slantPara ∧
    Nivat.LE2.dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (0 : ℤ)) = (0 : ℤ) ∧
    (∀ b ∈ slantPara,
      Nivat.LE2.dot (Nivat.ColleReg.expNormal ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (0 : ℤ)))
          ((0 : ℤ), (0 : ℤ))
        ≤ Nivat.LE2.dot (Nivat.ColleReg.expNormal ((0 : ℤ), (-1 : ℤ)) ((1 : ℤ), (0 : ℤ))) b) ∧
    (∀ z ∈ wS.erase ((0 : ℤ), (0 : ℤ)), ∀ j : ℕ,
      (j : ℤ) < Nivat.LE2.dot ((0 : ℤ), (1 : ℤ)) (z - ((0 : ℤ), (0 : ℤ))) →
        ∃ g ∈ slantPara, Nivat.LE2.dot ((0 : ℤ), (1 : ℤ)) g = (0 : ℤ) + (j : ℤ)) ∧
    ¬ (∀ w ∈ Nivat.ConeRegion.coneRegion slantPara ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (-1 : ℤ)),
        Nivat.LE2.dot ((0 : ℤ), (1 : ℤ)) w < (0 : ℤ) →
        ∀ z ∈ wS.erase ((0 : ℤ), (0 : ℤ)),
          (0 : ℤ) ≤ Nivat.LE2.dot ((0 : ℤ), (1 : ℤ)) (z + (w - ((0 : ℤ), (0 : ℤ)))) →
            z + (w - ((0 : ℤ), (0 : ℤ)))
              ∈ Nivat.LE2.halfStrip slantPara ((1 : ℤ), (0 : ℤ))) := by
  have hzmem : ∀ z ∈ wS.erase ((0 : ℤ), (0 : ℤ)), z = ((0 : ℤ), (2 : ℤ)) := by
    intro z hz
    rw [wS_erase, Finset.mem_singleton] at hz
    exact hz
  refine ⟨by norm_num [Nivat.det], by norm_num [Nivat.LE2.dot],
    by norm_num [Nivat.LE2.dot], slantPara_finite, slantPara_nonempty,
    slantPara_latticeConvex, slantPara_posArea, by decide,
    by rw [wS_erase]; exact Nivat.Colle37.latticeConvex_singleton _, ?_, ?_,
    mem_slantPara.mpr ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩,
    by norm_num [Nivat.LE2.dot], ?_, ?_, ?_⟩
  · intro z hz
    rw [hzmem z hz]
    norm_num [Nivat.LE2.dot]
  · intro b hb
    have hbm := mem_slantPara.mp hb
    simp only [Nivat.LE2.dot]
    omega
  · intro b hb
    have hbm := mem_slantPara.mp hb
    rw [mu_witness]
    simp only [Nivat.LE2.dot]
    omega
  · intro z hz j hj
    rw [hzmem z hz] at hj
    have hj2 : j < 2 := by
      simp only [Nivat.LE2.dot, Prod.fst_sub, Prod.snd_sub] at hj
      omega
    interval_cases j
    · exact ⟨((0 : ℤ), (0 : ℤ)),
        mem_slantPara.mpr ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩,
        by norm_num [Nivat.LE2.dot]⟩
    · exact ⟨((1 : ℤ), (1 : ℤ)),
        mem_slantPara.mpr ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩,
        by norm_num [Nivat.LE2.dot]⟩
  · intro hstrip
    have hw : ((0 : ℤ), (-1 : ℤ)) ∈
        Nivat.ConeRegion.coneRegion slantPara ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (-1 : ℤ)) := by
      rw [Nivat.ConeRegion.mem_coneRegion_iff]
      refine ⟨((0 : ℤ), (0 : ℤ)),
        mem_slantPara.mpr ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, 0, 1, ?_⟩
      simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul, Nat.cast_zero, Nat.cast_one]
      norm_num
    have hy : ((0 : ℤ), (2 : ℤ)) + (((0 : ℤ), (-1 : ℤ)) - ((0 : ℤ), (0 : ℤ)))
        = ((0 : ℤ), (1 : ℤ)) := by
      simp only [Prod.mk_sub_mk, Prod.mk_add_mk]
      norm_num
    have hz : ((0 : ℤ), (2 : ℤ)) ∈ wS.erase ((0 : ℤ), (0 : ℤ)) := by
      rw [wS_erase]; exact Finset.mem_singleton_self _
    have hlow : Nivat.LE2.dot ((0 : ℤ), (1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) < (0 : ℤ) := by
      norm_num [Nivat.LE2.dot]
    have hhi : (0 : ℤ) ≤ Nivat.LE2.dot ((0 : ℤ), (1 : ℤ))
        (((0 : ℤ), (2 : ℤ)) + (((0 : ℤ), (-1 : ℤ)) - ((0 : ℤ), (0 : ℤ)))) := by
      rw [hy]; norm_num [Nivat.LE2.dot]
    have hmem := hstrip _ hw hlow _ hz hhi
    rw [hy] at hmem
    obtain ⟨b, hb, t, hbt⟩ := hmem
    have h1 := congrArg Prod.fst hbt
    have h2 := congrArg Prod.snd hbt
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2
    obtain ⟨g1, g2, g3, g4⟩ := mem_slantPara.mp hb
    omega

/-! ## §15  The `hD` binder: a **positive** `vl`-period of `T u ξ` on the half-strip

**原文：b3_colle2.txt:774, :777, :781；Definition 3.4 at :414.**

`RegionSteps`' composers `wedgeResidualR_of_cone_of_enveloped` /
`wedgeResidualR_of_case1_of_cone` carry a binder

    hD : ∀ z ∈ D, (T e ξ) z = T (c • vl) (T e ξ) z

alongside `hc : 0 < c`, with `e := u` and `D` the (shifted) half-strip.  This section
discharges it from data the minimal-counterexample preamble already owns.

**Quantifier correspondence, term by term.**

* `hp_mem`, `hp_ne`, `hdet_vl` — `b3_colle2.txt:774`, the last sentence of the preamble:
  *"Propositions 2.10 and 2.12 imply that `x_per` and `y_per` are periodic with periods
  parallels to `ℓ`."*  `p ∈ Per xper` is "is a period of `x_per`"; `p ≠ 0` is "periodic"
  in the non-vacuous sense (`0` is a period of everything); `det p vl = 0` is "parallel to
  `ℓ`", `vl` being Collé's `v⃗_ℓ`.
* `hvl_prim` — not a hypothesis of the source sentence but of the *encoding*: "parallel to
  `ℓ`" is a statement about the line, and `det p vl = 0` recovers `p ∈ ℤ·vl` only when `vl`
  is a primitive vector on that line.  Every consumer of this file already carries
  `hvl_prim`, so this is bookkeeping, not an added assumption.
* `hagree` — `b3_colle2.txt:777`, the Case 1 hypothesis verbatim:
  `(T^u η)|H_B(ℓ) = x_per|H_B(ℓ)`.  `Nivat.LE2.halfStrip B' vl` is `H_B(ℓ)` (Definition 3.4,
  `:414`).
* the conclusion — `b3_colle2.txt:781`, **Claim 4.6**: *"`(T^u η)|𝓡_{ι-1}` is periodic with
  period parallel to `ℓ`"*, restricted from `𝓡_{ι-1}` down to `H_B(ℓ) ⊆ 𝓡_{ι-1}` (take
  `t = 0` in the definition of `𝓡_{ι-1}` at `:784`).  This is the *easy half* of Claim 4.6;
  the hard half is propagating it along `v⃗_{ℓ_{ι-1}}`, which is what §1–§14 are for.

**Why `0 < c` and not `c ≠ 0`.**  Not the consumer being fussy — it is forced, and the
witness `not_period_on_halfStrip_of_neg` below says so in the kernel.  `H_B(ℓ)` is the
**forward** sweep only (`:414` quantifies `t ∈ ℤ₊`), so it is closed under `+ c • vl` for
`0 ≤ c` and **not** for `c < 0`; with `c < 0` the point `z + c • vl` can leave the
half-strip, `hagree` does not reach it, and the transport through `xper`'s periodicity has
nothing to stand on.  The witness fails with `c • vl ∈ Per xper` *also* discharged, so the
obstruction is the one-sidedness of Definition 3.4, not a missing period.  Positivity costs
nothing: `Per xper` is an `AddSubgroup`, so one of `±p` is a positive multiple of `vl`.

**`B'` is arbitrary.**  Definition 3.4 asks `B` non-empty, finite and convex; none of that is
used, so the statement is given for a general `B' : Set (ℤ × ℤ)`.  The consumer instantiates
at `Nivat.LE2.shift (-((k : ℤ) • vl)) B` and transports with `halfStrip_shift`
(`RegionSteps.lean`); nothing extra falls out to be discharged.

⚠ **PROTOCOL.md §20 disclosure — read this before extending §15.**  Both steps below are
**already proved on-chain**, in Cprobe's `L1Line0.lean`:
`Nivat.L1Line0.add_zsmul_mem_halfStrip` (`L1Line0.lean:495`) is the closure step,
`Nivat.L1Line0.exists_pos_zsmul_mem_Per` (`L1Line0.lean:504`) the positive-multiple step, and
`Nivat.L1Line0.hD_of_agree_halfStrip` (`L1Line0.lean:517`) composes them.  `L1Line0` is
**not** in this file's import closure (177 modules) but **is** in `RegionSteps`' (225), so
the consumer can equally well discharge `hD` on the spot with those three.  The version below
exists only so that `StrictWindow` need not import the `L1` tree; the two helper steps are
`private` precisely so that no public name is duplicated. -/

section HD

variable {ξ xper : Config ℤ}

/-- The forward half-strip is closed under adding a **non-negative** multiple of its own
direction: `b3_colle2.txt:414` quantifies `t ∈ ℤ₊`, so `t + c` is again admissible exactly
when `0 ≤ c`.  Duplicate of `Nivat.L1Line0.add_zsmul_mem_halfStrip` (`L1Line0.lean:495`),
kept `private` — see the §15 disclosure. -/
private theorem add_zsmul_mem_halfStrip {B' : Set (ℤ × ℤ)} {vl z : ℤ × ℤ}
    (hz : z ∈ Nivat.LE2.halfStrip B' vl) {c : ℤ} (hc : 0 ≤ c) :
    z + c • vl ∈ Nivat.LE2.halfStrip B' vl := by
  obtain ⟨b, hb, t, rfl⟩ := hz
  refine ⟨b, hb, t + c.toNat, ?_⟩
  rw [Nat.cast_add, Int.toNat_of_nonneg hc, add_smul, add_assoc]

/-- A nonzero period parallel to a **primitive** `vl` yields a *positive* multiple of `vl`
that is still a period.  `hp_ne` is used exactly once, and only here: to rule out `c₀ = 0` in
`p = c₀ • vl`, which is the step that makes `0 < c` obtainable at all.  Duplicate of
`Nivat.L1Line0.exists_pos_zsmul_mem_Per` (`L1Line0.lean:504`), kept `private`. -/
private theorem exists_pos_zsmul_mem_Per {vl p : ℤ × ℤ} (hvl_prim : Nivat.Primitive vl)
    (hp_mem : p ∈ Nivat.Per xper) (hp_ne : p ≠ 0) (hdet_vl : Nivat.det p vl = 0) :
    ∃ c : ℤ, 0 < c ∧ c • vl ∈ Nivat.Per xper := by
  have hdet' : Nivat.det vl p = 0 := by rw [Nivat.det_comm, hdet_vl, neg_zero]
  obtain ⟨c₀, hc₀⟩ := Nivat.eq_zsmul_of_det_eq_zero hvl_prim hdet'
  have hc₀ne : c₀ ≠ 0 := by rintro rfl; exact hp_ne (by rw [hc₀, zero_smul])
  rcases lt_or_gt_of_ne hc₀ne with hneg | hpos
  · exact ⟨-c₀, by omega, by rw [neg_smul, ← hc₀]; exact (Nivat.Per xper).neg_mem hp_mem⟩
  · exact ⟨c₀, hpos, hc₀ ▸ hp_mem⟩

/-- **The `hD` binder on a plain `B`** — `b3_colle2.txt:774` + `:778`, Claim 4.6 restricted
to `H_B(ℓ)`.

This is the `hD` slot of `Nivat.ColleReg.wedgeResidualR_of_case1_of_cone_at_base`
(`RegionSteps.lean`), with `e := u`.  At `k = 0` the shift layer collapses and the binder is
stated on `B` itself, so no `Nivat.LE2.shift` appears here.

**Quantifier correspondence.**

* `hagree` — `b3_colle2.txt:778`, Case 1's standing hypothesis verbatim: *"suppose there
  exists `u ∈ ℤ²` such that `(T^u η)|H_B(ℓ) = x_per|H_B(ℓ)`"*.  `Nivat.LE2.halfStrip B vl`
  is `H_B(ℓ)` (Definition 3.4, `:414`), `vl` being Collé's `v⃗_ℓ`.
* `hper` — `b3_colle2.txt:774`, end of the preamble paragraph: *"Propositions 2.10 and 2.12
  imply that `x_per` and `y_per` are periodic with periods parallels to `ℓ`"*.  `c • vl` is
  that period; this is the unfolded form of `c • vl ∈ Nivat.Per xper`
  (`Nivat.mem_Per_iff`), taken pointwise so that no `AddSubgroup` plumbing is needed at the
  call site.
* `hc` — the team's positive-`c` convention.  **Only `0 ≤ c` is used**; `0 < c` is taken
  because the consumer carries it, not because the proof needs strictness.  Non-negativity
  itself is *not* dispensable: see `not_period_on_halfStrip_of_neg`.

**The mechanism, and the one fact it rests on.**  `T h x z = x (z + h)`
(`Nivat/Defs/Config.lean:50`), so the goal at `z` reads `ξ (z + u) = ξ (z + c • vl + u)`.
`hagree` supplies the left side as `xper z`; it supplies the right side as
`xper (z + c • vl)` **only if `z + c • vl` is again in the half-strip**, and
`H_B(ℓ) = {b + t • vl : b ∈ B, t : ℕ}` is closed under `+ c • vl` exactly for `0 ≤ c`
(the `ℕ`-index goes `t ↦ t + c.toNat`).  `hper` then closes the two sides.

**Sign check, done before the statement was committed** (hard rule 10).  `T`'s convention is
`T h x z = x (z + h)`, *not* `x (z - h)`, so the translate that must stay inside the
half-strip is `z + c • vl` with `c` **positive** — the convention comes out in favour of the
shape as dispatched, and no flip to `c < 0` is needed.  Numerically, with `vl = (1,0)`,
`c = 2`, `B = {(0,0)}`, `z = (3,0) = (0,0) + 3 • vl`: `z + c • vl = (5,0) = (0,0) + 5 • vl`,
`ℕ`-index `3 ↦ 5`, still in `H_B(ℓ)`.  With `c = -2` and `z = (0,0)` the same step asks for
`t : ℕ` with `(t : ℤ) = -2` and there is none — that failure is what
`not_period_on_halfStrip_of_neg` records in the kernel. -/
theorem hD_of_case1_of_periodic {B : Set (ℤ × ℤ)} {vl u : ℤ × ℤ} {c : ℤ}
    (hc : 0 < c)
    (hagree : ∀ z ∈ Nivat.LE2.halfStrip B vl, Nivat.T u ξ z = xper z)
    (hper : ∀ z, xper z = Nivat.T (c • vl) xper z) :
    ∀ z ∈ Nivat.LE2.halfStrip B vl,
      (Nivat.T u ξ) z = Nivat.T (c • vl) (Nivat.T u ξ) z := by
  intro z hz
  rw [Nivat.T_apply (c • vl), hagree z hz,
    hagree _ (add_zsmul_mem_halfStrip hz hc.le), ← Nivat.T_apply (c • vl) xper z, ← hper z]

/-- **The `hD` binder, discharged** (`b3_colle2.txt:781`, Claim 4.6 on `H_B(ℓ)`).

From the preamble's parallel period (`:774`) and the Case 1 agreement (`:777`), `T u ξ` is
`c • vl`-periodic on `H_B(ℓ)` for some **positive** `c` — the `hc`/`hD` pair of
`Nivat.ColleReg.wedgeResidualR_of_case1_of_cone` (`RegionSteps.lean`) with `e := u`.

Differs from `hD_of_case1_of_periodic` only in producing `c` rather than receiving it: the
periodicity is extracted from `hp_mem`/`hp_ne`/`hdet_vl` instead of being handed over.

`B'` is arbitrary — no finiteness, non-emptiness or convexity of Definition 3.4 is used, so
the consumer may instantiate at a shifted `B` without discharging anything extra. -/
theorem exists_period_on_halfStrip {B' : Set (ℤ × ℤ)} {vl p u : ℤ × ℤ}
    (hp_mem : p ∈ Nivat.Per xper) (hp_ne : p ≠ 0) (hvl_prim : Nivat.Primitive vl)
    (hdet_vl : Nivat.det p vl = 0)
    (hagree : ∀ z ∈ Nivat.LE2.halfStrip B' vl, Nivat.T u ξ z = xper z) :
    ∃ c : ℤ, 0 < c ∧
      ∀ z ∈ Nivat.LE2.halfStrip B' vl,
        (Nivat.T u ξ) z = Nivat.T (c • vl) (Nivat.T u ξ) z :=
  let ⟨c, hc, hper⟩ := exists_pos_zsmul_mem_Per hvl_prim hp_mem hp_ne hdet_vl
  ⟨c, hc, hD_of_case1_of_periodic hc hagree (fun z => (Nivat.Per.apply hper z).symm)⟩

/-- **`0 < c` is not removable: the same statement with `c ≠ 0` is false.**

Witness: `B' = {(0,0)}`, `vl = (1,0)`, `u = 0`, `p = (1,0)`, `c = -1`, `xper ≡ 0`, and
`ξ` the indicator of the single cell `(-1,0)`.  `H_{B'}(ℓ) = {(t,0) : t ∈ ℤ₊}` misses
`(-1,0)`, so `hagree` holds; but `T ((-1) • vl) (T u ξ)` reads `ξ` at `(-1,0)` from the
half-strip point `(0,0)`.

Every hypothesis of `exists_period_on_halfStrip` is discharged on the witness
(PROTOCOL.md §7), and so is `c • vl ∈ Per xper` — **which is the point**: the obstruction is
not a missing period but the one-sidedness of Definition 3.4 (`b3_colle2.txt:414`, `t ∈ ℤ₊`).
Per hard rule 10 the named missing hypothesis is `0 ≤ c`, i.e. that `c • vl` points along
`v⃗_ℓ` rather than against it. -/
theorem not_period_on_halfStrip_of_neg :
    ∃ (ξ' xper' : Config ℤ) (B' : Set (ℤ × ℤ)) (vl p u : ℤ × ℤ) (c : ℤ),
      p ∈ Nivat.Per xper' ∧ p ≠ 0 ∧ Nivat.Primitive vl ∧ Nivat.det p vl = 0 ∧
        (∀ z ∈ Nivat.LE2.halfStrip B' vl, Nivat.T u ξ' z = xper' z) ∧
        c ≠ 0 ∧ c • vl ∈ Nivat.Per xper' ∧
        ¬ (∀ z ∈ Nivat.LE2.halfStrip B' vl,
            (Nivat.T u ξ') z = Nivat.T (c • vl) (Nivat.T u ξ') z) := by
  classical
  refine ⟨fun z => if z = ((-1 : ℤ), (0 : ℤ)) then (1 : ℤ) else 0, fun _ => (0 : ℤ),
    {((0 : ℤ), (0 : ℤ))}, ((1 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (0 : ℤ)), -1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Nivat.mem_Per_iff).mpr rfl
  · intro h; exact absurd (congrArg Prod.fst h) (by norm_num)
  · exact isCoprime_one_left
  · norm_num [Nivat.det]
  · rintro z ⟨b, hb, t, rfl⟩
    rw [Set.mem_singleton_iff] at hb
    subst hb
    have hne : ((0 : ℤ), (0 : ℤ)) + (t : ℤ) • ((1 : ℤ), (0 : ℤ)) + ((0 : ℤ), (0 : ℤ))
        ≠ ((-1 : ℤ), (0 : ℤ)) := by
      intro h
      have := congrArg Prod.fst h
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] at this
      omega
    simp only [Nivat.T_apply]
    rw [if_neg hne]
  · norm_num
  · exact (Nivat.mem_Per_iff).mpr rfl
  · intro h
    have hmem : ((0 : ℤ), (0 : ℤ)) ∈
        Nivat.LE2.halfStrip ({((0 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)) ((1 : ℤ), (0 : ℤ)) :=
      ⟨((0 : ℤ), (0 : ℤ)), Set.mem_singleton _, 0, by simp⟩
    have h0 := h _ hmem
    simp only [Nivat.T_apply] at h0
    norm_num at h0

end HD

end Nivat.StrictWindow

#print axioms Nivat.StrictWindow.mem_halfStrip_iff_level_and_mu
#print axioms Nivat.StrictWindow.hstrip_of_fit_window
#print axioms Nivat.StrictWindow.hstrip_iff_fit_window
#print axioms Nivat.StrictWindow.hstrip_of_lean_of_occupancy
#print axioms Nivat.StrictWindow.not_hstrip_of_occupancy_without_mu

#print axioms Nivat.StrictWindow.hD_of_case1_of_periodic
#print axioms Nivat.StrictWindow.exists_period_on_halfStrip
#print axioms Nivat.StrictWindow.not_period_on_halfStrip_of_neg

#print axioms Nivat.StrictWindow.coneRegion_add_natSmul_step
#print axioms Nivat.StrictWindow.exists_mem_halfStrip_step_not_mem
#print axioms Nivat.StrictWindow.occupancy_of_hstrip

#print axioms Nivat.StrictWindow.hbase_of_cone_halfStrip_of_hmono_of_argmax
#print axioms Nivat.StrictWindow.exists_argmax_base

#print axioms Nivat.StrictWindow.dot_translate_le_sub_one
#print axioms Nivat.StrictWindow.translate_window_le_of_strict_argmax
#print axioms Nivat.StrictWindow.mem_seed_union_lines
#print axioms Nivat.StrictWindow.hwinL_of_strict_argmax
#print axioms Nivat.StrictWindow.hbase_at_of_strict_argmax
#print axioms Nivat.StrictWindow.dot_le_of_hapex
#print axioms Nivat.StrictWindow.not_hstrict_of_hapex
#print axioms Nivat.StrictWindow.strict_of_hapex_pos
#print axioms Nivat.StrictWindow.cone_upper_subset_halfStrip
#print axioms Nivat.StrictWindow.hbase_of_cone_argmax
#print axioms Nivat.StrictWindow.exists_strict_argmin_of_no_edge_parallel
#print axioms Nivat.StrictWindow.not_hwinL_cone_ascending
#print axioms Nivat.StrictWindow.no_edge_parallel_witness
#print axioms Nivat.StrictWindow.hbase_of_cone_halfStrip
#print axioms Nivat.StrictWindow.level_le_of_mem_halfStrip
#print axioms Nivat.StrictWindow.hwinL_cone_of_hstrict_of_hfit
#print axioms Nivat.StrictWindow.not_hfit_of_finite
#print axioms Nivat.StrictWindow.hwinL_cone_halfStrip_of_hstrict_of_geom
#print axioms Nivat.StrictWindow.hbase_of_cone_halfStrip_of_geom
#print axioms Nivat.StrictWindow.not_coneRegion_subset_halfStrip_union_lines
#print axioms Nivat.StrictWindow.coneRegion_inter_level_subset_halfStrip_iff_hmono
#print axioms Nivat.StrictWindow.coneRegion_subset_halfStrip_union_lines_of_hmono
#print axioms Nivat.StrictWindow.hbase_of_cone_halfStrip_of_hmono
#print axioms Nivat.StrictWindow.cover_witness_has_no_edge_parallel_to_neg_ell
