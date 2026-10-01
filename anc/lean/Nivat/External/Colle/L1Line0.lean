/-
Copyright (c) 2026 Nivat formalisation project. All rights reserved.
-/
import Nivat.External.Colle.L1Claim
import Nivat.External.Colle.L1Prim
import Nivat.External.Colle.CaseSplit
import Nivat.External.Colle.SfinBound

/-!
# L1 — the `line0` seed on `chainFull` (the `hline` slot of `exists_L1MaxBResidual_of_wedgeAt_split`)

Lane Cprobe's exclusive file (2026-09-19).  Target: the binder
```
hline : ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
  ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
  ∃ τ : ℤ, ∀ z ∈ derivedQ ε u' (S.image (· + v)),
    τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
    τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N)
```
of `Nivat.ColleReg.L1Claim.exists_L1MaxBResidual_of_wedgeAt_split` (`L1Claim.lean`).

## What is proved (all kernel-checked, receipts at the end of the file)

* **`τ` is not a joint parameter.**  `chainFull B vl u' b₀ n = wedgeFull B vl u' ∩
  halfPlaneGE (expNormal u' vl) (expLevel u' vl b₀ n)`; the level half is `τ`-free
  (`dot_expNormal_u'`, unconditional) and the wedge half holds for every `τ ≥ -uCoord z`
  (`mem_wedgeFull_of_le`), so the line seed exists **iff** the finite level residual
  `∀ z ∈ Q, expLevel n ≤ dot en z ∧ expLevel n ≤ dot en z + c` holds (`exists_line_iff`, an
  iff — the residual is exact, not a sufficient condition).  Once it holds, *every* `τ ≥ τ₀`
  works (`exists_tau₀`), and `Straddle` is upward-closed in `τ` too (`straddle_mono_tau`), so
  the shared `τ` of `hsel` is a `max`, never a negotiation.
* **The residual is `c`-sign-sensitive.**  For `c < 0` it fails as soon as `Q` touches the
  level `expLevel n` (`not_exists_line_of_neg`).  For `0 ≤ c` the second conjunct is free.
  **Team convention (team-lead ruling, 2026-09-19): WLOG `0 < c`.**  The sign of `c` is free
  at the leaf: `c` rides on `p = c • vl`, and `p ↦ -p` preserves `hp_mem`/`hp_ne`/`hdet_vl`
  while `hbase` transports by `periodOn_neg_zsmul` — a call-site move, not a hypothesis on the
  model.  ⚠ The flip must be on `p`, **not on `vl`**: `Case1 ξ xper S vl → Case1 … (-vl)` is
  **false** (`not_case1_symm`, §5 below) because `Case1`'s half-strip is forward-only
  (`halfStrip`, `LatticeEdges.lean`).
* **A sufficient placement.**  With the cut side `εOf u' vl` (for which
  `cutNormal (εOf u' vl) u' = toReal (-(expNormal u' vl))`, `cutNormal_εOf`), `derivedQ` is
  the part of `S₁` strictly above `S₁`'s lowest `expNormal`-level.  If every point of `S₁`
  sits at level `≥ expLevel (k+N₀) - 1` (`hmin`) then `derivedQ` sits at level
  `≥ expLevel (k+N₀)` (`levels_of_placement`), which is the residual with `0 ≤ c`.  This is
  Collé's `𝒯 ∖ ℓ'_𝒯 ⊂ 𝓡^N_I` with `ℓ'_𝒯` on the single line
  `chainFull (N+1) ∖ chainFull N` (`chainFull_diff_subset_line`).
* **The placement is realisable by the `v`-valve**: `expNormal u' vl` is primitive
  (`primitive_expNormal`), so `S.image (· + v)` can be put with its lowest level exactly at
  any prescribed `L` (`exists_shift_min_level`).
* **The `∀ N` in the slot is a single index**: `Nivat.L1Prim.maximal_index_unique` identifies
  any `N` satisfying the two `PeriodOn` premises with the given `N₀` (`hline_of_placement`).
* **§27 feeding term**: `exists_L1MaxBResidual_of_placement` applies
  `exists_L1MaxBResidual_of_wedgeAt_split` with `hline := hline_of_placement …` and
  `ε := εOf u' vl`; what remains after this file is Cconv's `hstraddle` plus the placement
  hypotheses (`hN₀`, `hN₀1`, `hmin`, `0 < c`).

## C-group data: every extra requirement is an explicit binder

`hbase` / `hline` / `hstraddle` share the data `B b₀ k c e u'` (Cclaim's C group).  What this
file asks of that data, and nothing else, appears as binders of `hline_of_placement`:
`hb₀ : b₀ ∈ B`, `hunimod : det u' vl = ±1`, `hc : 0 < c`, and the placement `hmin` (which
constrains `v`, via `S₁ = S.image (· + v)`, relative to `b₀`/`k`/`N₀`).  `ε` is fixed to
`εOf u' vl`.  Nothing is hidden in a proof.

## What is **not** proved here

* `hstraddle` (Cconv), `hbase` (AnfpL), `hlev` (L1B) — untouched, still binders.
* That the placement `hmin` is *compatible* with `hstraddle` — this file only shows the
  placement is realisable and discharges `hline` under it.  If Cconv's `Straddle` needs the
  top face *exactly* on `expLevel (k+N₀) - 1`, `exists_shift_min_level` provides that too
  (its second conjunct); if it needs a different placement, `exists_line_iff` says exactly
  what `hline` then demands.
* Nothing about `hξ`: no statement in this file has `IsMinimalCounterexample` in a
  hypothesis except the final feeding term, which merely forwards it.
* §5's `ξR` is a toy model (values in `{0,1}`, periodic in `y`), not a counterexample to
  anything with `hξ`; `not_case1_symm` is a `¬∀`, it kills the *route* "prove one end and flip
  `vl`", it says nothing about any specific instance (§25).
-/

set_option autoImplicit false

namespace Nivat.L1Line0

open Nivat Nivat.LE2 Nivat.ColleReg Nivat.ColleReg.L1Data Nivat.Colle41

/-! ## §1  Coordinates in the unimodular basis `(vl, u')` -/

section Coord

variable {u' vl : ℤ × ℤ}

/-- The `u'`-coordinate of `z - b₀` in the basis `(vl, u')` (`det u' vl = ±1`). -/
def uCoord (u' vl b₀ z : ℤ × ℤ) : ℤ := -(det u' vl) * det vl (z - b₀)

theorem det_sq (hunimod : det u' vl = 1 ∨ det u' vl = -1) : det u' vl * det u' vl = 1 := by
  rcases hunimod with h | h <;> rw [h] <;> ring

/-- `z = b₀ + A • vl + uCoord • u'` for some `A`. -/
theorem exists_decomp (hunimod : det u' vl = 1 ∨ det u' vl = -1) (b₀ z : ℤ × ℤ) :
    ∃ A C : ℤ, z = b₀ + A • vl + C • u' ∧ C = uCoord u' vl b₀ z := by
  have hsq := det_sq hunimod
  refine ⟨det u' vl * det u' (z - b₀), uCoord u' vl b₀ z, ?_, rfl⟩
  ext
  · simp only [uCoord, det, Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.fst_sub,
      Prod.snd_sub] at hsq ⊢
    linear_combination (-(z.1 - b₀.1)) * hsq
  · simp only [uCoord, det, Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.fst_sub,
      Prod.snd_sub] at hsq ⊢
    linear_combination (-(z.2 - b₀.2)) * hsq

/-- Moving along `vl` does not change the `u'`-coordinate. -/
theorem uCoord_add_zsmul_vl (b₀ z : ℤ × ℤ) (c : ℤ) :
    uCoord u' vl b₀ (z + c • vl) = uCoord u' vl b₀ z := by
  simp only [uCoord, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **The wedge half of `line` is free for every large `τ`**: `τ • u' + z ∈ wedgeFull B vl u'`
as soon as the `u'`-coordinate `τ + uCoord z` is nonnegative. -/
theorem mem_wedgeFull_of_le {B : Set (ℤ × ℤ)} {b₀ : ℤ × ℤ} (hb₀ : b₀ ∈ B)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) {τ : ℤ} {z : ℤ × ℤ}
    (hτ : 0 ≤ τ + uCoord u' vl b₀ z) : τ • u' + z ∈ wedgeFull B vl u' := by
  obtain ⟨A, C, hz, hC⟩ := exists_decomp hunimod b₀ z
  refine ⟨b₀ + A • vl, mem_fullSweep_iff.mpr ⟨b₀, hb₀, A, rfl⟩,
    (τ + uCoord u' vl b₀ z).toNat, ?_⟩
  rw [Int.toNat_of_nonneg hτ, add_smul, ← hC, hz]
  abel

end Coord

/-! ## §2  The level half is `τ`-free -/

section Level

variable {u' vl : ℤ × ℤ}

theorem dot_expNormal_zsmul_add (τ : ℤ) (z : ℤ × ℤ) :
    dot (expNormal u' vl) (τ • u' + z) = dot (expNormal u' vl) z := by
  rw [dot_add, dot_smul_right, dot_expNormal_u', mul_zero, zero_add]

theorem dot_expNormal_add_zsmul_vl (hunimod : det u' vl = 1 ∨ det u' vl = -1) (z : ℤ × ℤ)
    (c : ℤ) : dot (expNormal u' vl) (z + c • vl) = dot (expNormal u' vl) z + c := by
  rw [dot_add, dot_smul_right, dot_expNormal_vl hunimod, mul_one]

theorem mem_chainFull_iff {B : Set (ℤ × ℤ)} {b₀ z : ℤ × ℤ} {n : ℕ} :
    z ∈ chainFull B vl u' b₀ n ↔
      z ∈ wedgeFull B vl u' ∧ expLevel u' vl b₀ n ≤ dot (expNormal u' vl) z := Iff.rfl

/-- **`line ⟹ level residual`**: read off the second component of `chainFull`. -/
theorem levels_of_line {B : Set (ℤ × ℤ)} {b₀ : ℤ × ℤ} {n : ℕ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) {Q : Finset (ℤ × ℤ)} {c τ : ℤ}
    (h : ∀ z ∈ Q, τ • u' + z ∈ chainFull B vl u' b₀ n ∧
      τ • u' + z + c • vl ∈ chainFull B vl u' b₀ n) :
    ∀ z ∈ Q, expLevel u' vl b₀ n ≤ dot (expNormal u' vl) z ∧
      expLevel u' vl b₀ n ≤ dot (expNormal u' vl) z + c := by
  intro z hz
  obtain ⟨h1, h2⟩ := h z hz
  have e1 := (mem_chainFull_iff.mp h1).2
  have e2 := (mem_chainFull_iff.mp h2).2
  rw [dot_expNormal_zsmul_add] at e1
  rw [add_assoc, dot_expNormal_zsmul_add, dot_expNormal_add_zsmul_vl hunimod] at e2
  exact ⟨e1, e2⟩

/-- **`level residual ⟹ line for every large `τ`**: `τ₀` is a max over the finite `Q`. -/
theorem exists_tau₀ {B : Set (ℤ × ℤ)} {b₀ : ℤ × ℤ} (hb₀ : b₀ ∈ B)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) {n : ℕ} {Q : Finset (ℤ × ℤ)} {c : ℤ}
    (hlev : ∀ z ∈ Q, expLevel u' vl b₀ n ≤ dot (expNormal u' vl) z ∧
      expLevel u' vl b₀ n ≤ dot (expNormal u' vl) z + c) :
    ∃ τ₀ : ℤ, ∀ τ : ℤ, τ₀ ≤ τ → ∀ z ∈ Q,
      τ • u' + z ∈ chainFull B vl u' b₀ n ∧ τ • u' + z + c • vl ∈ chainFull B vl u' b₀ n := by
  obtain ⟨M, hM⟩ := Finset.exists_le (Q.image fun z => -uCoord u' vl b₀ z)
  refine ⟨M, fun τ hτ z hz => ?_⟩
  have hz' : -uCoord u' vl b₀ z ≤ M := hM _ (Finset.mem_image_of_mem _ hz)
  obtain ⟨l1, l2⟩ := hlev z hz
  refine ⟨mem_chainFull_iff.mpr ⟨mem_wedgeFull_of_le hb₀ hunimod (by omega), ?_⟩,
    mem_chainFull_iff.mpr ⟨?_, ?_⟩⟩
  · rw [dot_expNormal_zsmul_add]; exact l1
  · rw [add_assoc]
    exact mem_wedgeFull_of_le hb₀ hunimod (by rw [uCoord_add_zsmul_vl]; omega)
  · rw [add_assoc, dot_expNormal_zsmul_add, dot_expNormal_add_zsmul_vl hunimod]; exact l2

/-- **The exact residual of the line seed on `chainFull`** — an iff, no `τ` on the right. -/
theorem exists_line_iff {B : Set (ℤ × ℤ)} {b₀ : ℤ × ℤ} (hb₀ : b₀ ∈ B)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (n : ℕ) (Q : Finset (ℤ × ℤ)) (c : ℤ) :
    (∃ τ : ℤ, ∀ z ∈ Q,
      τ • u' + z ∈ chainFull B vl u' b₀ n ∧ τ • u' + z + c • vl ∈ chainFull B vl u' b₀ n) ↔
    ∀ z ∈ Q, expLevel u' vl b₀ n ≤ dot (expNormal u' vl) z ∧
      expLevel u' vl b₀ n ≤ dot (expNormal u' vl) z + c :=
  ⟨fun ⟨_, h⟩ => levels_of_line hunimod h,
    fun h => let ⟨τ₀, h'⟩ := exists_tau₀ hb₀ hunimod h; ⟨τ₀, h' τ₀ le_rfl⟩⟩

/-- **Boundary of the residual (honest negative)**: with `c < 0`, a single point of `Q` on the
level `expLevel n` kills every `τ`. -/
theorem not_exists_line_of_neg {B : Set (ℤ × ℤ)} {b₀ : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) {n : ℕ} {Q : Finset (ℤ × ℤ)} {c : ℤ}
    {z : ℤ × ℤ} (hz : z ∈ Q) (hlev : dot (expNormal u' vl) z = expLevel u' vl b₀ n)
    (hc : c < 0) :
    ¬ ∃ τ : ℤ, ∀ z ∈ Q,
      τ • u' + z ∈ chainFull B vl u' b₀ n ∧ τ • u' + z + c • vl ∈ chainFull B vl u' b₀ n :=
  fun ⟨_, h⟩ => by
    have := (levels_of_line hunimod h z hz).2
    omega

/-- `Straddle` is upward-closed in `τ` (it only quantifies `∀ t₀, τ ≤ t₀ → …`), so a `τ`
produced for the line seed can always be raised to whatever `Straddle` needs. -/
theorem straddle_mono_tau {x : Config ℤ} {Rlo Rhi : Set (ℤ × ℤ)} {S₁ Q : Finset (ℤ × ℤ)}
    {u u' : ℤ × ℤ} {c τ τ' : ℤ} (h : Nivat.L1Region.Straddle x Rlo Rhi S₁ Q u u' c τ)
    (hle : τ ≤ τ') : Nivat.L1Region.Straddle x Rlo Rhi S₁ Q u u' c τ' :=
  fun g hg hgQ t₀ ht₀ => h g hg hgQ t₀ (le_trans hle ht₀)

/-- **The executing tool of the `0 < c` convention.**  `PeriodOn` is symmetric under
`h ↦ -h`, so wherever `c` enters `ofWedgeAt` (`hbase`; `hinf` likewise) the sign is free.
At the leaf this is `p ↦ -p`: `Per` is an `AddSubgroup`, `det (-p) vl = -det p vl`. -/
theorem periodOn_neg_zsmul {x : Config ℤ} {R : Set (ℤ × ℤ)} {c : ℤ} {w : ℤ × ℤ}
    (h : PeriodOn x R (c • w)) : PeriodOn x R ((-c) • w) := by
  rw [neg_smul]
  exact h.neg

theorem not_periodOn_neg_zsmul {x : Config ℤ} {R : Set (ℤ × ℤ)} {c : ℤ} {w : ℤ × ℤ}
    (h : ¬ PeriodOn x R (c • w)) : ¬ PeriodOn x R ((-c) • w) :=
  fun h' => h (by simpa using periodOn_neg_zsmul h')

end Level

/-! ## §3  The cut side and `derivedQ` in integer terms -/

section Cut

variable {u' vl : ℤ × ℤ}

theorem expNormal_eq (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    expNormal u' vl = perp u' ∨ expNormal u' vl = -perp u' := by
  rcases hunimod with h | h
  · left; rw [expNormal, h, one_smul]; rfl
  · right; rw [expNormal, h, neg_one_smul]; rfl

theorem primitive_expNormal (hu' : Primitive u') (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    Primitive (expNormal u' vl) := by
  rcases expNormal_eq hunimod with h | h
  · rw [h]; exact primitive_perp hu'
  · rw [h]
    show IsCoprime (-(perp u').1) (-(perp u').2)
    exact (primitive_perp hu').neg_neg

/-- The side of the cut whose normal is `-(expNormal u' vl)`: `derivedQ` then consists of the
points of `S₁` strictly **above** its lowest `expNormal`-level. -/
def εOf (u' vl : ℤ × ℤ) : Bool := decide (det u' vl = -1)

theorem cutNormal_εOf (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    cutNormal (εOf u' vl) u' = toReal (-(expNormal u' vl)) := by
  rcases hunimod with h | h
  · have hε : εOf u' vl = false := by simp [εOf, h]
    rw [hε, cutNormal, if_neg Bool.false_ne_true, expNormal, h, one_smul]
    rfl
  · have hε : εOf u' vl = true := by simp [εOf, h]
    rw [hε, cutNormal, if_pos rfl, expNormal, h, neg_one_smul, neg_neg]
    rfl

/-- A point of `derivedQ (εOf u' vl) u' S₁` lies strictly above some point of `S₁` in the
`expNormal`-level (integer form of the strict `<` in `derivedQ`, `L1Cut.lean:98`). -/
theorem exists_lt_of_mem_derivedQ (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {S₁ : Finset (ℤ × ℤ)} {z : ℤ × ℤ} (hz : z ∈ derivedQ (εOf u' vl) u' S₁) :
    z ∈ S₁ ∧ ∃ y ∈ S₁, dot (expNormal u' vl) y < dot (expNormal u' vl) z := by
  unfold derivedQ at hz
  rw [Finset.mem_filter] at hz
  obtain ⟨hz, hlt⟩ := hz
  refine ⟨hz, ?_⟩
  unfold levelMax at hlt
  rw [dif_pos ⟨z, hz⟩] at hlt
  obtain ⟨y, hy, hy'⟩ :=
    Finset.exists_mem_eq_sup' ⟨z, hz⟩ (fun w => inner2 (cutNormal (εOf u' vl) u') w)
  rw [hy', cutNormal_εOf hunimod, inner2_toReal, inner2_toReal, dot_neg_left, dot_neg_left]
    at hlt
  have h' : -dot (expNormal u' vl) z < -dot (expNormal u' vl) y := by exact_mod_cast hlt
  exact ⟨y, hy, by omega⟩

/-- **Sufficient placement**: all of `S₁` at level `≥ expLevel n - 1` and `0 ≤ c` give the
residual for `derivedQ (εOf u' vl) u' S₁` (levels are integers, so "strictly above a level
`≥ L - 1`" is "`≥ L`"). -/
theorem levels_of_placement {b₀ : ℤ × ℤ} (hunimod : det u' vl = 1 ∨ det u' vl = -1) {n : ℕ}
    {c : ℤ} (hc : 0 ≤ c) {S₁ : Finset (ℤ × ℤ)}
    (hmin : ∀ s ∈ S₁, expLevel u' vl b₀ n - 1 ≤ dot (expNormal u' vl) s) :
    ∀ z ∈ derivedQ (εOf u' vl) u' S₁, expLevel u' vl b₀ n ≤ dot (expNormal u' vl) z ∧
      expLevel u' vl b₀ n ≤ dot (expNormal u' vl) z + c := by
  intro z hz
  obtain ⟨_, y, hy, hlt⟩ := exists_lt_of_mem_derivedQ hunimod hz
  have := hmin y hy
  constructor <;> omega

/-- **The `v`-valve realises the placement**: for any `L`, some translate `S.image (· + v)`
has its lowest `expNormal`-level exactly `L`.  Needs `Primitive (expNormal u' vl)`, which is
free from `Primitive u'` (`primitive_expNormal`) — no `gcd` obstruction here, unlike a general
normal `m` (`L1Shift.lean`). -/
theorem exists_shift_min_level (hu' : Primitive u') (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    {S : Finset (ℤ × ℤ)} (hS : S.Nonempty) (L : ℤ) :
    ∃ v : ℤ × ℤ, (∀ s ∈ S.image (· + v), L ≤ dot (expNormal u' vl) s) ∧
      ∃ s ∈ S.image (· + v), dot (expNormal u' vl) s = L := by
  obtain ⟨z₀, hz₀, hmin⟩ := S.exists_min_image (fun z => dot (expNormal u' vl) z) hS
  obtain ⟨v, hv⟩ := Nivat.HalfPlaneFamily.exists_dot_eq_of_primitive
    (primitive_expNormal hu' hunimod) (L - dot (expNormal u' vl) z₀)
  refine ⟨v, ?_, z₀ + v, Finset.mem_image_of_mem (· + v) hz₀, ?_⟩
  · intro s hs
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hs
    show L ≤ dot (expNormal u' vl) (z + v)
    have := hmin z hz
    rw [dot_add, hv]
    omega
  · rw [dot_add, hv]; ring

end Cut

/-! ## §4  The slot, and the §27 feeding term -/

section Slot

variable {u' vl : ℤ × ℤ}

theorem monotone_chainFull_shift (B : Set (ℤ × ℤ)) (vl u' b₀ : ℤ × ℤ) (k : ℕ) :
    Monotone (fun n => chainFull B vl u' b₀ (k + n)) :=
  fun _ _ hab =>
    Nivat.L1Region.cut_mono (expLevel_antitone u' vl b₀) (Nat.add_le_add_left hab k)

/-- **`hline` of `exists_L1MaxBResidual_of_wedgeAt_split`, under the placement and the team
convention `0 < c`.**  The `∀ N` of the slot collapses to the given maximal index `N₀` by
`maximal_index_unique`; the seed is then `exists_tau₀` at the residual
`levels_of_placement`.  Every demand on the C-group data is a binder here. -/
theorem hline_of_placement {ξ : Config ℤ} {e : ℤ × ℤ} {B : Set (ℤ × ℤ)} {b₀ : ℤ × ℤ}
    (hb₀ : b₀ ∈ B) (hunimod : det u' vl = 1 ∨ det u' vl = -1) {c : ℤ} (hc : 0 < c)
    {k N₀ : ℕ}
    (hN₀ : PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N₀)) (c • vl))
    (hN₀1 : ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N₀ + 1))) (c • vl))
    {S₁ : Finset (ℤ × ℤ)}
    (hmin : ∀ s ∈ S₁, expLevel u' vl b₀ (k + N₀) - 1 ≤ dot (expNormal u' vl) s) :
    ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
      ∃ τ : ℤ, ∀ z ∈ derivedQ (εOf u' vl) u' S₁,
        τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
        τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N) := by
  intro N hN hN1
  have hNN : N = N₀ :=
    Nivat.L1Prim.maximal_index_unique (monotone_chainFull_shift B vl u' b₀ k) hN hN1 hN₀ hN₀1
  subst hNN
  obtain ⟨τ₀, h⟩ := exists_tau₀ hb₀ hunimod (levels_of_placement hunimod hc.le hmin)
  exact ⟨τ₀, h τ₀ le_rfl⟩

/-- **§27 feeding term.**  `exists_L1MaxBResidual_of_wedgeAt_split` with `hline` discharged by
`hline_of_placement` and `ε := εOf u' vl`.  What remains: Cconv's `hstraddle` (verbatim from
the split, at this `ε`) and the placement data (`N₀`, `hN₀`, `hN₀1`, `hmin`, `0 < c`).  Not a
new entry point — it *is* the split entry, partially applied. -/
theorem exists_L1MaxBResidual_of_placement
    {ξ : Config ℤ} {ℓ : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (hξ : IsMinimalCounterexample ξ) (d : Nivat.Colle35.DecompDataZ ξ)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (hvl_prim : Primitive vl) (hdet_ℓ : dot ℓ vl = 0)
    {e v b₀ : ℤ × ℤ} {c : ℤ} {U B : Set (ℤ × ℤ)}
    (hEnv : EnvOf U B) (hb₀ : b₀ ∈ B)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) (hc : 0 < c)
    (hlev : Nivat.RegionSweep.LevelInterval B vl) (k : ℕ)
    (hbase : PeriodOn (T e ξ) (chainFull B vl u' b₀ k) (c • vl))
    {N₀ : ℕ}
    (hN₀ : PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N₀)) (c • vl))
    (hN₀1 : ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N₀ + 1))) (c • vl))
    (hmin : ∀ s ∈ S.image (· + v),
      expLevel u' vl b₀ (k + N₀) - 1 ≤ dot (expNormal u' vl) s)
    (hstraddle : ∀ N : ℕ, PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + N)) (c • vl) →
      ¬ PeriodOn (T e ξ) (chainFull B vl u' b₀ (k + (N + 1))) (c • vl) →
      ∀ τ : ℤ,
        (∀ z ∈ derivedQ (εOf u' vl) u' (S.image (· + v)),
          τ • u' + z ∈ chainFull B vl u' b₀ (k + N) ∧
          τ • u' + z + c • vl ∈ chainFull B vl u' b₀ (k + N)) →
        Nivat.L1Region.Straddle (T e ξ) (chainFull B vl u' b₀ (k + N))
          (chainFull B vl u' b₀ (k + (N + 1))) (S.image (· + v))
          (derivedQ (εOf u' vl) u' (S.image (· + v))) vl u' c τ) :
    ∃ (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
      (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c),
      S₁ = S.image (· + v) ∧
      Nivat.ColleReg.L1Data.MaxBResidual (ξ := ξ) ε u u' c τ S₁ F :=
  Nivat.ColleReg.L1Claim.exists_L1MaxBResidual_of_wedgeAt_split hξ d hℓ_nel hℓ_neg hSgen
    hvl_prim hdet_ℓ (εOf u' vl) hEnv hb₀ hunimod hc.ne' hlev k hbase
    (hline_of_placement hb₀ hunimod hc hN₀ hN₀1 hmin) hstraddle

end Slot

/-! ## §5  `Case1` is not symmetric under `vl ↦ -vl` (why the flip goes on `p`)

Landed from `tmp/case1_sym.lean` by team-lead's ruling (2026-09-19).  `Case1 ξ xper S vl`
(`CaseSplit.lean`) is one-sided: its `halfStrip B vl` (`LatticeEdges.lean`) is forward-only.
A toy model witnesses that the reverse direction can fail while the forward one holds.  This is
a `¬∀` (§25): it refutes the *route* "prove conjuncts 14/15/16 at one end and flip `vl`", not
any statement carrying `hξ`.  The asset here is the `halfStrip` one-sidedness, not the model. -/

section Case1Sym

/-- `ξ = 1` on the left half-plane `{z.1 < 0}`, `0` on the right. -/
def ξR : Config ℤ := fun z => if 0 ≤ z.1 then 0 else 1

/-- `x_per = 0`. -/
def xper0 : Config ℤ := fun _ => 0

/-- The window: the unit square as a `Finset`. -/
def SF : Finset (ℤ × ℤ) := ({0, 1} : Finset ℤ) ×ˢ ({0, 1} : Finset ℤ)

theorem coe_SF : ((SF : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = box (0, 0) (1, 1) := by
  ext z
  simp only [SF, Finset.coe_product, Set.mem_prod, Finset.coe_insert, Finset.coe_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff, mem_box]
  omega

theorem envOf_SF : EnvOf (SF : Set (ℤ × ℤ)) (box (0, 0) (1, 1)) := by
  rw [coe_SF]
  exact enveloped_refl _ (isLatticeConvexRegion_box _ _)

/-- **Positive direction holds**: `vl = (1,0)`, the forward half-strip lies in `{0 ≤ z.1}`,
where `ξR = 0 = xper0`. -/
theorem case1_pos : Case1 ξR xper0 SF (1, 0) := by
  refine ⟨box (0, 0) (1, 1), envOf_SF, 0, ?_⟩
  rintro z ⟨b, hb, t, rfl⟩
  rw [mem_box] at hb
  simp only [T, ξR, xper0, Prod.fst_add, Prod.smul_fst, smul_eq_mul, add_zero]
  rw [if_pos (by omega)]

/-- Any `E(SF)`-enveloped `B` is nonempty: it has as many edges as the square (four), and an
edge has a nontrivial face inside `B`. -/
theorem nonempty_of_envOf {B : Set (ℤ × ℤ)} (h : EnvOf (SF : Set (ℤ × ℤ)) B) : B.Nonempty := by
  have hE : (E B).encard = (E (SF : Set (ℤ × ℤ))).encard := h.2
  rw [coe_SF, E_box (by norm_num) (by norm_num)] at hE
  have hne : (E B).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h0
    rw [h0, Set.encard_empty] at hE
    have h1 : ({(1, 0), (-1, 0), (0, 1), (0, -1)} : Set (ℤ × ℤ)) = ∅ :=
      Set.encard_eq_zero.mp hE.symm
    have : ((1 : ℤ), (0 : ℤ)) ∈ ({(1, 0), (-1, 0), (0, 1), (0, -1)} : Set (ℤ × ℤ)) := by simp
    rw [h1] at this
    exact this
  obtain ⟨n, hn⟩ := hne
  obtain ⟨x, hx, -⟩ := (mem_E_iff.mp hn).2
  exact ⟨x, face_subset B n hx⟩

/-- **Negative direction fails**: for every enveloped `B` and every shift `u`, the backward
half-strip from a point `b ∈ B` eventually enters `{z.1 + u.1 < 0}`, where `T u ξR = 1 ≠ 0`. -/
theorem not_case1_neg : ¬ Case1 ξR xper0 SF (-(1, 0)) := by
  rintro ⟨B, hB, u, hu⟩
  obtain ⟨b, hb⟩ := nonempty_of_envOf hB
  have hmem : b + (((b.1 + u.1 + 1).toNat : ℕ) : ℤ) • (-((1 : ℤ), (0 : ℤ))) ∈
      halfStrip B (-(1, 0)) :=
    ⟨b, hb, _, rfl⟩
  have := hu _ hmem
  have ht : b.1 + u.1 + 1 ≤ (((b.1 + u.1 + 1).toNat : ℕ) : ℤ) := Int.self_le_toNat _
  simp only [T, ξR, xper0, Prod.fst_add, Prod.smul_fst, Prod.fst_neg, smul_eq_mul, mul_neg,
    mul_one] at this
  rw [if_neg (by omega)] at this
  exact one_ne_zero this

/-- The two together: `Case1` is **not** symmetric under `vl ↦ -vl`.  Refutes the route, not
an instance (§25). -/
theorem not_case1_symm :
    ¬ ∀ (ξ xper : Config ℤ) (S : Finset (ℤ × ℤ)) (vl : ℤ × ℤ),
      Case1 ξ xper S vl → Case1 ξ xper S (-vl) :=
  fun h => not_case1_neg (h _ _ _ _ case1_pos)

end Case1Sym

/-! ## §6  `hcase1`'s second conjunct is an `hD` producer

`hcase1 : Case1 ξ xper d.Sphi vl` (the last binder of `exists_L1MaxBResidual`) unpacks to
`∃ B, EnvOf ↑S B ∧ ∃ u, ∀ z ∈ halfStrip B vl, T u ξ z = xper z` — agreement of `T u ξ` with
`xper` on the whole forward `vl`-sweep of `B`.  `HbaseBridge.hbase_of_sweep_self`'s seed slot is
`hD : ∀ z ∈ D, (T e ξ) z = T (c • vl) (T e ξ) z` — `c • vl`-periodicity of `T e ξ` on `D`.

**Honest answer: these are not the same statement, and one yields the other under exactly one
extra binder, which the chain already has.**  Agreement with `xper` on a set transports any
period of `xper` that keeps the set inside itself; `halfStrip B vl` is closed under `+ c • vl`
for `0 ≤ c` (`add_zsmul_mem_halfStrip`), so what is needed is `c • vl ∈ Per xper` with
`0 ≤ c`.  That is produced from the leaf's own binders `hp_mem : p ∈ Per xper`, `hp_ne`,
`hdet_vl : det p vl = 0`, `hvl_prim` by `exists_pos_zsmul_mem_Per`: `p` is an integer multiple
of the primitive `vl` (`Nivat.eq_zsmul_of_det_eq_zero`, `Lattice/Primitive.lean`), and `Per` is
a subgroup so the multiple can be taken positive.  This is also where the team's `0 < c`
convention comes from for free: the positive multiple *is* the `c`.

C-group commitments this makes (explicit, not hidden): `e := u` (the `u` of `hcase1`),
`B := ` the `B` of `hcase1` (so `hEnv : EnvOf U B` of the split is met with `U := ↑d.Sphi`),
`D := halfStrip B vl`, `c := ` the positive multiple.  What it does **not** give: `hK`
(`chainFull B vl u' b₀ 0 ⊆ halfStrip B vl ∪ ⋃ range enum` — `chainFull` also sweeps backward
along `vl` and along `u'`, so `halfStrip` covers only a part of it; that is the `hfringe`/`enum`
question, Aface's), `hwin`, `hgen`. -/

section Case1ToHD

variable {ξ xper : Config ℤ} {vl : ℤ × ℤ}

/-- The forward half-strip is closed under adding a nonnegative multiple of its direction. -/
theorem add_zsmul_mem_halfStrip {B : Set (ℤ × ℤ)} {z : ℤ × ℤ} (hz : z ∈ halfStrip B vl)
    {c : ℤ} (hc : 0 ≤ c) : z + c • vl ∈ halfStrip B vl := by
  obtain ⟨b, hb, t, rfl⟩ := hz
  refine ⟨b, hb, t + c.toNat, ?_⟩
  rw [Nat.cast_add, Int.toNat_of_nonneg hc, add_smul, add_assoc]

/-- **The extra binder, produced from the leaf's own data**: a *positive* multiple of `vl` is a
period of `xper`.  `det p vl = 0` with `vl` primitive makes `p = c₀ • vl`; `p ≠ 0` makes
`c₀ ≠ 0`; `Per` is a subgroup so `|c₀| • vl ∈ Per xper`. -/
theorem exists_pos_zsmul_mem_Per {p : ℤ × ℤ} (hvl_prim : Primitive vl) (hp_mem : p ∈ Per xper)
    (hp_ne : p ≠ 0) (hdet_vl : det p vl = 0) : ∃ c : ℤ, 0 < c ∧ c • vl ∈ Per xper := by
  have hdet' : det vl p = 0 := by rw [det_comm, hdet_vl, neg_zero]
  obtain ⟨c₀, hc₀⟩ := Nivat.eq_zsmul_of_det_eq_zero hvl_prim hdet'
  have hc₀ne : c₀ ≠ 0 := by rintro rfl; exact hp_ne (by rw [hc₀, zero_smul])
  rcases lt_or_gt_of_ne hc₀ne with hneg | hpos
  · refine ⟨-c₀, by omega, ?_⟩
    rw [neg_smul, ← hc₀]
    exact (Per xper).neg_mem hp_mem
  · exact ⟨c₀, hpos, hc₀ ▸ hp_mem⟩

/-- **Agreement with a periodic configuration transports the period**: on `halfStrip B vl`,
`T u ξ = xper` and `xper` is `c • vl`-periodic with `0 ≤ c`, hence `T u ξ` is `c • vl`-periodic
there — verbatim the shape of `hbase_of_sweep_self`'s `hD` with `e := u`, `D := halfStrip B vl`. -/
theorem hD_of_agree_halfStrip {B : Set (ℤ × ℤ)} {u : ℤ × ℤ}
    (hu : ∀ z ∈ halfStrip B vl, T u ξ z = xper z) {c : ℤ} (hc : 0 ≤ c)
    (hper : c • vl ∈ Per xper) :
    ∀ z ∈ halfStrip B vl, (T u ξ) z = T (c • vl) (T u ξ) z := by
  intro z hz
  rw [T_apply (c • vl), hu z hz, hu _ (add_zsmul_mem_halfStrip hz hc), Per.apply hper]

/-- **`hcase1` destructured into `hD` form.**  Everything on the right is either free
(`obtain` on `hcase1`) or produced from the leaf's binders (`exists_pos_zsmul_mem_Per`). -/
theorem exists_hD_of_case1 {S : Finset (ℤ × ℤ)} {p : ℤ × ℤ}
    (hcase1 : Case1 ξ xper S vl) (hvl_prim : Primitive vl) (hp_mem : p ∈ Per xper)
    (hp_ne : p ≠ 0) (hdet_vl : det p vl = 0) :
    ∃ B : Set (ℤ × ℤ), EnvOf (S : Set (ℤ × ℤ)) B ∧ ∃ u : ℤ × ℤ, ∃ c : ℤ, 0 < c ∧
      c • vl ∈ Per xper ∧ (∀ z ∈ halfStrip B vl, T u ξ z = xper z) ∧
      ∀ z ∈ halfStrip B vl, (T u ξ) z = T (c • vl) (T u ξ) z := by
  obtain ⟨B, hEnv, u, hu⟩ := hcase1
  obtain ⟨c, hc, hper⟩ := exists_pos_zsmul_mem_Per hvl_prim hp_mem hp_ne hdet_vl
  exact ⟨B, hEnv, u, c, hc, hper, hu, hD_of_agree_halfStrip hu hc.le hper⟩

/-- Also directly: `T u ξ` is `c • vl`-periodic on the half-strip in `PeriodOn` form (no sweep
needed for the half-strip itself; the sweep is only needed to leave it). -/
theorem periodOn_halfStrip_of_agree {B : Set (ℤ × ℤ)} {u : ℤ × ℤ}
    (hu : ∀ z ∈ halfStrip B vl, T u ξ z = xper z) {c : ℤ} (hc : 0 ≤ c)
    (hper : c • vl ∈ Per xper) : PeriodOn (T u ξ) (halfStrip B vl) (c • vl) :=
  Nivat.Colle43.periodOn_of_agree_T (hD_of_agree_halfStrip hu hc hper)

/-- **§27 feeding term.**  `hbase_of_sweep_self` with `e := u`, `D := halfStrip B vl`, and its
`hD` slot filled by `hD_of_agree_halfStrip`.  What remains: `hgen`, `enum`, `hwin`, `hK`. -/
theorem hbase_of_sweep_of_case1_agree {B : Set (ℤ × ℤ)} {u : ℤ × ℤ}
    (hu : ∀ z ∈ halfStrip B vl, T u ξ z = xper z) {c : ℤ} (hc : 0 ≤ c)
    (hper : c • vl ∈ Per xper)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : Nivat.Colle.GeneratesAt ξ S a)
    {u' b₀ : ℤ × ℤ}
    (enum : ℕ → ℕ → ℤ × ℤ)
    (hwin : ∀ i j : ℕ, ∀ z ∈ S.erase a,
      z + (enum i j - a) ∈
        halfStrip B vl ∪ (⋃ i' ∈ {i' | i' < i}, Set.range (enum i')) ∪
          (enum i '' {j' | j' < j}))
    (hK : chainFull B vl u' b₀ 0 ⊆ halfStrip B vl ∪ (⋃ i, Set.range (enum i))) :
    PeriodOn (T u ξ) (chainFull B vl u' b₀ 0) (c • vl) :=
  Nivat.HbaseBridge.hbase_of_sweep_self hgen (hD_of_agree_halfStrip hu hc hper) enum hwin hK

end Case1ToHD

/-! ## §7  The backward `vl`-sweep is outside slice `0` once `b₀` is `expNormal`-maximal

Team-lead's probe (`tmp/chainback_probe.lean`, 2026-09-19), landed here by ruling.  For
`z = b + k • vl + r • u'` the level is exactly `dot (expNormal u' vl) b + k`
(`dot_expNormal_decomp`), and the cut `expLevel u' vl b₀ 0 = dot m b₀` says `dot m b₀ ≤ dot m b + k`.
If `b₀` is `m`-maximal in `B` this forces `0 ≤ k`, so
`chainFull B vl u' b₀ 0 ⊆ sweep (halfStrip B vl) u'` — the `-vl` half of `fullSweep` never
enters slice `0`, and §6's `D := halfStrip B vl` covers everything except the `u'`-direction.

**Only `⊆` is stated.**  Equality would need `b₀` `m`-minimal as well (`B` flat in `m`); do not
use the reverse inclusion, it is false in general.

**The `b₀` is produced, not assumed** (`exists_b₀_max_of_envOf`): `B` is finite on-chain via
`Nivat.L1Sfin.hSfin_of_decompDataZ` (`SfinBound.lean`), which is stated for `Enveloped`, and
`EnvOf U T` is *definitionally* `Enveloped U T` (`LatticeEdges.lean`, `envOf_iff : … := Iff.rfl`)
— so `hcase1`'s `EnvOf ↑d.Sphi B` feeds it with no bridge.  Nonemptiness of `B` comes from
`E B = E ↑d.Sphi ≠ ∅` (`nonempty_of_enveloped_Sphi`, the first five steps of `SfinBound` reused).

⚠ **C-group constraint made explicit**: this pins `b₀` to the `expNormal u' vl`-argmax of `B`.
`expLevel u' vl b₀` indexes the whole level ladder, so every consumer of `chainFull … b₀ …`
inherits the choice; flagged to Aface and L3win. -/

section BackSweep

variable {u' vl : ℤ × ℤ}

theorem dot_expNormal_decomp (hunimod : det u' vl = 1 ∨ det u' vl = -1) (b : ℤ × ℤ) (k : ℤ)
    (r : ℕ) :
    dot (expNormal u' vl) (b + k • vl + (r : ℤ) • u') = dot (expNormal u' vl) b + k := by
  rw [dot_add, dot_smul_right, dot_expNormal_u', mul_zero, add_zero,
    dot_expNormal_add_zsmul_vl hunimod]

theorem expLevel_zero (b₀ : ℤ × ℤ) : expLevel u' vl b₀ 0 = dot (expNormal u' vl) b₀ := by
  simp [expLevel]

/-- **Slice `0` lies in the forward half-strip swept along `u'`**, provided `b₀` is
`expNormal`-maximal in `B`. -/
theorem chainFull_zero_subset_sweep_halfStrip {B : Set (ℤ × ℤ)} {b₀ : ℤ × ℤ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hb₀max : ∀ b ∈ B, dot (expNormal u' vl) b ≤ dot (expNormal u' vl) b₀) :
    chainFull B vl u' b₀ 0 ⊆ Nivat.RegionSweep.sweep (halfStrip B vl) u' := by
  rintro z ⟨hzw, hzlev⟩
  obtain ⟨g, hg, r, rfl⟩ := hzw
  obtain ⟨b, hb, k, rfl⟩ := mem_fullSweep_iff.mp hg
  have hlev := dot_expNormal_decomp hunimod b k r
  have hb₀ := hb₀max b hb
  have hge : dot (expNormal u' vl) b₀ ≤ dot (expNormal u' vl) b + k := by
    have h2 : expLevel u' vl b₀ 0 ≤ dot (expNormal u' vl) (b + k • vl + (r : ℤ) • u') := hzlev
    rwa [expLevel_zero, hlev] at h2
  have hk0 : 0 ≤ k := by omega
  refine ⟨b + k • vl, ⟨b, hb, k.toNat, ?_⟩, r, rfl⟩
  rw [Int.toNat_of_nonneg hk0]

/-- Every finite nonempty `B` has an `expNormal`-argmax. -/
theorem exists_expNormal_max {B : Set (ℤ × ℤ)} (hfin : B.Finite) (hne : B.Nonempty) :
    ∃ b₀ ∈ B, ∀ b ∈ B, dot (expNormal u' vl) b ≤ dot (expNormal u' vl) b₀ :=
  Set.exists_max_image B (fun b => dot (expNormal u' vl) b) hfin hne

open Nivat.Colle35 Pointwise in
/-- `E ↑d.Sphi` is nonempty (first five steps of `SfinBound.hSfin_of_decompDataZ`, reused). -/
theorem exists_mem_E_Sphi {ξ : Config ℤ} (d : DecompDataZ ξ) :
    ∃ n, n ∈ E (d.Sphi : Set (ℤ × ℤ)) := by
  classical
  obtain ⟨n, -, hnmem, -, -⟩ := exists_two_nonparallel_edge_normals d.hm d.h_ne d.h_dir
  have hConv : Conv d.Sphi = Conv (zonoF Finset.univ d.h) := by
    rw [d.Sphi_eq]
    exact Conv_supp_prod_eq_Conv_zonoF Finset.univ d.h (fun i _ => d.h_ne i)
  have hEeq : E (d.Sphi : Set (ℤ × ℤ)) = E (↑(zonoF Finset.univ d.h) : Set (ℤ × ℤ)) :=
    E_congr_of_Conv_eq hConv
  have hcoe : (↑(zonoF Finset.univ d.h) : Set (ℤ × ℤ))
      = ∑ i ∈ Finset.univ, segOf (d.h i) := coe_zonoF _ _
  rw [hcoe] at hEeq
  exact ⟨n, hEeq ▸ hnmem⟩

open Nivat.Colle35 in
/-- Any `E(𝒮_φ)`-enveloped `B` is nonempty: it has the same (nonempty) edge set, and an edge's
face is a nonempty subset of `B`. -/
theorem nonempty_of_enveloped_Sphi {ξ : Config ℤ} (d : DecompDataZ ξ) {B : Set (ℤ × ℤ)}
    (hB : Enveloped (d.Sphi : Set (ℤ × ℤ)) B) : B.Nonempty := by
  obtain ⟨n, hn⟩ := exists_mem_E_Sphi d
  have hUfin : (E (d.Sphi : Set (ℤ × ℤ))).Finite := finite_E_of_finite d.Sphi.finite_toSet
  have hE : E B = E (d.Sphi : Set (ℤ × ℤ)) := Enveloped.E_eq hUfin hB
  rw [← hE] at hn
  obtain ⟨x, hx, -⟩ := (mem_E_iff.mp hn).2
  exact ⟨x, face_subset B n hx⟩

open Nivat.Colle35 in
/-- **The `b₀` producer.**  From `hcase1`'s `EnvOf ↑d.Sphi B` (definitionally `Enveloped`),
`B` is finite (`SfinBound`) and nonempty, so it has an `expNormal`-argmax `b₀`, and slice `0`
of the chain based at that `b₀` lies inside `sweep (halfStrip B vl) u'`. -/
theorem exists_b₀_max_of_envOf {ξ : Config ℤ} (d : DecompDataZ ξ) {B : Set (ℤ × ℤ)}
    (hEnv : EnvOf (d.Sphi : Set (ℤ × ℤ)) B) (hunimod : det u' vl = 1 ∨ det u' vl = -1) :
    ∃ b₀ ∈ B, (∀ b ∈ B, dot (expNormal u' vl) b ≤ dot (expNormal u' vl) b₀) ∧
      chainFull B vl u' b₀ 0 ⊆ Nivat.RegionSweep.sweep (Nivat.LE2.halfStrip B vl) u' := by
  have hfin : B.Finite := Nivat.L1Sfin.hSfin_of_decompDataZ d B hEnv
  obtain ⟨b₀, hb₀, hmax⟩ := exists_expNormal_max (u' := u') (vl := vl) hfin
    (nonempty_of_enveloped_Sphi d hEnv)
  exact ⟨b₀, hb₀, hmax, chainFull_zero_subset_sweep_halfStrip hunimod hmax⟩

end BackSweep

/-! ## §8  No `u'`-period of `xper` exists on the chain (negative fact, an asset)

Landed from `tmp/uperiod_probe.lean` (2026-09-19, team-lead ruling 18:35).  Team-lead asked whether
the `Case1` agreement propagates along `u'`, i.e. whether `sweep (halfStrip B vl) u'` could serve
as §6's `D`.  It cannot by agreement with `xper`: the last conjunct of `exists_preamble_pair`'s
`hpartner` (`RegionSteps.lean`, `∃ yper nℓ cz g, … ∧ ¬ ∃ h h', det h h' ≠ 0 ∧ PeriodicOnWith xper
U h ∧ PeriodicOnWith xper U h'` with `U := {z | cz ≤ dot nℓ z}`) forces **every** period of
`xper` to be parallel to `vl` (`det_eq_zero_of_mem_Per`), so no `u'` with `det u' vl = ±1` is a
period (`not_mem_Per_of_unimod`).  The `u'`-direction is therefore the sweep's job
(`enum`/`hwin`), matching Collé Claim 4.6 (`b3_colle2.txt:783-800`), not `hD`'s.

The `hnd` binder is stated in exactly the shape `exists_preamble_pair` produces; the §27 shape
check that destructures that theorem's output (`shape_check`) stays in `tmp/uperiod_probe.lean`
because it needs `import RegionSteps`, which is downstream of `L1Claim`.

⚠ This is not vacuous under `hξ`: `hnd` is a *conclusion* component of `exists_preamble_pair`,
not a hypothesis on a minimal counterexample. -/

section UPeriod

/-- **Every period of `xper` is parallel to `vl`**, given the `hpartner` conjunct "`xper` is not
doubly periodic on `U`": a period `q` with `det q vl ≠ 0` together with `p ∥ vl` would be two
non-parallel periods, and global periods restrict to any `U`. -/
theorem det_eq_zero_of_mem_Per {xper : Config ℤ} {U : Set (ℤ × ℤ)} {p vl q : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hp_mem : p ∈ Per xper) (hp_ne : p ≠ 0) (hdet_vl : det p vl = 0)
    (hnd : ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
      Nivat.Colle35.PeriodicOnWith xper U h ∧ Nivat.Colle35.PeriodicOnWith xper U h')
    (hq : q ∈ Per xper) : det q vl = 0 := by
  by_contra hne
  apply hnd
  have hqne : q ≠ 0 := by rintro rfl; exact hne (by simp [det])
  refine ⟨p, q, ?_, ⟨hp_ne, fun g _ _ => Per.apply hp_mem g⟩,
    ⟨hqne, fun g _ _ => Per.apply hq g⟩⟩
  obtain ⟨c₀, hc₀⟩ := Nivat.eq_zsmul_of_det_eq_zero hvl_prim
    (by rw [det_comm, hdet_vl, neg_zero] : det vl p = 0)
  have hc₀ne : c₀ ≠ 0 := by rintro rfl; exact hp_ne (by rw [hc₀, zero_smul])
  have hpq : det p q = -(c₀ * det q vl) := by
    rw [hc₀]; simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  rw [hpq]
  exact neg_ne_zero.mpr (mul_ne_zero hc₀ne hne)

/-- In particular no `u'` with `det u' vl = ±1` is a period of `xper`: `sweep (halfStrip B vl) u'`
cannot be made periodic by agreement with `xper`. -/
theorem not_mem_Per_of_unimod {xper : Config ℤ} {U : Set (ℤ × ℤ)} {p vl u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hp_mem : p ∈ Per xper) (hp_ne : p ≠ 0) (hdet_vl : det p vl = 0)
    (hnd : ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
      Nivat.Colle35.PeriodicOnWith xper U h ∧ Nivat.Colle35.PeriodicOnWith xper U h')
    (hunimod : det u' vl = 1 ∨ det u' vl = -1) : u' ∉ Per xper := fun h => by
  have := det_eq_zero_of_mem_Per hvl_prim hp_mem hp_ne hdet_vl hnd h
  rcases hunimod with h1 | h1 <;> omega

end UPeriod

end Nivat.L1Line0

section Receipts

#print axioms Nivat.L1Line0.exists_decomp
#print axioms Nivat.L1Line0.mem_wedgeFull_of_le
#print axioms Nivat.L1Line0.levels_of_line
#print axioms Nivat.L1Line0.exists_tau₀
#print axioms Nivat.L1Line0.exists_line_iff
#print axioms Nivat.L1Line0.not_exists_line_of_neg
#print axioms Nivat.L1Line0.straddle_mono_tau
#print axioms Nivat.L1Line0.periodOn_neg_zsmul
#print axioms Nivat.L1Line0.not_periodOn_neg_zsmul
#print axioms Nivat.L1Line0.primitive_expNormal
#print axioms Nivat.L1Line0.cutNormal_εOf
#print axioms Nivat.L1Line0.exists_lt_of_mem_derivedQ
#print axioms Nivat.L1Line0.levels_of_placement
#print axioms Nivat.L1Line0.exists_shift_min_level
#print axioms Nivat.L1Line0.hline_of_placement
#print axioms Nivat.L1Line0.exists_L1MaxBResidual_of_placement
#print axioms Nivat.L1Line0.case1_pos
#print axioms Nivat.L1Line0.nonempty_of_envOf
#print axioms Nivat.L1Line0.not_case1_neg
#print axioms Nivat.L1Line0.not_case1_symm
#print axioms Nivat.L1Line0.add_zsmul_mem_halfStrip
#print axioms Nivat.L1Line0.exists_pos_zsmul_mem_Per
#print axioms Nivat.L1Line0.hD_of_agree_halfStrip
#print axioms Nivat.L1Line0.exists_hD_of_case1
#print axioms Nivat.L1Line0.periodOn_halfStrip_of_agree
#print axioms Nivat.L1Line0.hbase_of_sweep_of_case1_agree
#print axioms Nivat.L1Line0.dot_expNormal_decomp
#print axioms Nivat.L1Line0.chainFull_zero_subset_sweep_halfStrip
#print axioms Nivat.L1Line0.exists_mem_E_Sphi
#print axioms Nivat.L1Line0.nonempty_of_enveloped_Sphi
#print axioms Nivat.L1Line0.exists_b₀_max_of_envOf
#print axioms Nivat.L1Line0.det_eq_zero_of_mem_Per
#print axioms Nivat.L1Line0.not_mem_Per_of_unimod

end Receipts
