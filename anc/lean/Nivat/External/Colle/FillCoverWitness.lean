/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ShellSweep
import Nivat.External.Colle.ChainAssemble

/-!
# `fillCover` at `(i, i₀, ε) = (2, 1, 1)` on `ShellSweep`'s data: single sweep vs `:518`

Lane Aenvfix, 2026-09-19.  Counterexample archive (`not_*` declarations); it has no consumer
by design and is not on the main-theorem chain.  Landed from `tmp/aenvfix_fillCover_wit.lean`
(independently re-run by Amink, 7/7 `[propext, Classical.choice, Quot.sound]`).  Everything is
on the `m = 3` data of `Nivat/External/Colle/ShellSweep.lean`: window `hexA`,
`Â_i := Ai i = hexShape (2i) (2i) i i 0`, `Â_∞ := quad`, `v_{ℓ_{J-1}} = (0,-1)`, `n_J = (0,1)`,
`c_J = 0`, `-v_{ℓ_{J+1}} = (-1,-1)`.

## Which signature's closure is refuted (leaf-C discipline)

The negative results refute the **`fillCover` binder of `ChainDataGeom.ofParts`
(`ChainAssemble.lean`) as it stands on 2026-09-19**, i.e. with the shell pinned to the single
sweep `shell i ε := MaxEnv.shell (hatOf A kk vl i) vJ1 nJ cJ ε`, instantiated at
`A := Ai`, `kk ≡ 0`, `vl := vJ1 := (0,-1)`, `nJ := (0,1)`, `cJ := 0`, `S := hexF`,
`gen ∈ {(0,0), (1,0)}`.  `fillCover_binder_false` below feeds the binder's exact text into the
elaborator (PROTOCOL §27) rather than asserting the shapes agree in prose.  It says nothing
about a `ChainDataGeom` (the binder is quantified over all `(i, i₀, ε)`; one instance fails),
and nothing about the `:518` port's `fillCover`, which §2 shows *holds* for `gen = (1,0)`.

## What is measured

1. **Negative (§1).**  With the shell pinned to the single sweep
   `MaxEnv.shell (Ai i) (0,-1) (0,1) 0 ε` (what `ChainAssemble.ofParts` currently does),
   `fillCover` at `(i, i₀, ε) = (2, 1, 1)` is **false for every `gen` with `gen.1 ≤ 1`** — in
   particular for both bottom-face points `(0,0)` and `(1,0)` of `hexA`.  Witness: `(4,0)` is
   in the sweep (from `(4,2) ∈ Ai 2`) but no generation step ever produces a point with
   `x = 4` outside `Ai 2`, because `(2,1) ∈ hexA` forces `t.1 ≤ 2` for every translate.
2. **Positive (§2).**  With the shell replaced by the literal `:518` object
   `ShellMink.shellInter (Ai i) (Â_∞^{(ε)}) (-1,-1)`, the same `fillCover` instance at
   `(2, 1, 1)` **holds for `gen = (1,0)`**, by `subset_genClosure_of_rank` with the trivial rank:
   the only new site `(1,-1)` is `(1,0) + (0,-1)` and all six other window points land in
   `Ai 2 ∪ Â_1^{(1)}`.
3. **Caveat, also kernel (§2).**  For `gen = (0,0)` the `:518` instance at `(2,1,1)` is
   **false** too: `(1,-1)` would need `(2,-1)`, which is outside the `:518` object.  So
   `fillCover` on the `:518` port is `gen`-dependent; the generating point must be the
   `v_J`-forward end of the bottom face.  On this data `v_J = (1,0)`, so that end is
   `a' = (1,0)` (`FaceBlock.lex'`, the `v_J`-**maximal** endpoint), not `a = (0,0)`.  This is
   the receipt behind `ofParts`'s `gen_eq : gen = F.a'` binder.
4. **`shellSubStrip` on the `:518` object (§3)**, re-proved for the new object as required
   (not transported from `ShellMink.not_shellSubStrip_of_transverse_sweep`, which is about
   `MaxEnv.shell` only): with `vl := (0,-1)`, `kk ≡ 0`, `B i := Ai i`, one has
   `shellInter (Ai i) (Â_∞^{(ε)}) (-1,-1) ⊆ halfStrip (Ai i) (0,-1)` for all `i ε`.
   **Scope:** this is the `J = ι + 1` configuration (`v_ℓ = v_{ℓ_{J-1}}`, `det vl vJ1 = 0`);
   it says nothing about `J > ι + 1`.
5. **守卫辨识（§5，lane-leafa-gen 2026-09-25）.**  §1 反驳的是 `ofParts` 的**无守卫** binder
   （见上一节，`:19-20` 原文已如此写明）。迁移后链上的字段带 `EnvOf` 守卫，而在 §1 所用的
   同一台架上取 `w := vJ1`，那条守卫**对一切 `ε`、一切 `i` 都为假**（`not_envOf_shell_Ai`）：
   塌成的单次 sweep 丢了 `(1,-1)` 边。⟹ 带守卫的 `fillCover` 字段在那里是**空真**
   （`fillCover_field_vacuous_at_vJ1`），§1 咬不到它；真正被 §5 否掉的是 **`shellEnv`**
   （`not_shellEnv_field_at_vJ1`）。⛔ 凡把 §1 直接当成「`w := vJ1` ⟹ `fillCover` 字段为假」
   的引用都要改引 `not_shellEnv_field_at_vJ1`。
6. **`det vl w ≠ 0` 不可从 `shellEnv` 导出（§6，lane-leafa-gen 2026-09-25，集成者第 228 轮派）.**
   换成**方窗口** `sq1` 后，`w := vJ1`（即 `det vl w = 0`）的 `shellEnv` 字段**成立**
   （`shellEnv_field_at_vJ1_square`，`ε = 1`、`i₀ = 0`、对一切 `i`），16 条链上前提全兑现
   ⟹ `not_shellEnv_imp_det_ne_zero`。机制的一般形是 `E_shell_eq_of_shellEnv_at_vJ1`：
   `w := vl` 那一格逼出的是 `E(单次 sweep) = E ↑S`，成败只看 `E ↑S` 里有没有一条被 `vJ1`
   抬高、又不是 `-nJ` 的法向（`hexF` 有、`sq1` 没有）。⟹ §5 的 `det_vl_w_discriminates`
   降级为台架现象。

Reading, not kernel fact: the `(2,1,1)` instance is one `(i, i₀, ε)`; `ofParts` quantifies
over all three.
-/

set_option autoImplicit false

namespace Nivat.FillCoverWit

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.ShellSweep

/-- An upper bound for `genClosure`: any `Y ⊇ X` closed under one generation step. -/
theorem genClosure_subset_of_closed {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ} {X Y : Set (ℤ × ℤ)}
    (hX : X ⊆ Y)
    (hcl : ∀ t : ℤ × ℤ, (∀ b ∈ S.erase gen, b + t ∈ Y) → gen + t ∈ Y) :
    genClosure S gen X ⊆ Y := by
  have key : ∀ n, genFill S gen X n ⊆ Y := by
    intro n
    induction n with
    | zero => exact hX
    | succ n ih =>
      rintro z (hz | ⟨t, rfl, ht⟩)
      · exact ih hz
      · exact hcl t fun b hb => ih (ht b hb)
  exact Set.iUnion_subset key

/-- `hexA` as a `Finset`, for the `S` argument of `genFill`. -/
def hexF : Finset (ℤ × ℤ) := {(0, 0), (1, 0), (2, 1), (2, 2), (1, 2), (0, 1), (1, 1)}

theorem coe_hexF : (↑hexF : Set (ℤ × ℤ)) = ShellMink.hexA := by
  rw [hexA_eq_hexShape]
  ext ⟨x, y⟩
  simp only [hexF, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, Prod.mk.injEq, mem_hexShape]
  omega

theorem mem_hexF_two_one {gen : ℤ × ℤ} (h : gen.1 ≤ 1) : ((2 : ℤ), (1 : ℤ)) ∈ hexF.erase gen := by
  refine Finset.mem_erase.2 ⟨?_, by simp [hexF]⟩
  intro heq; rw [← heq] at h; simp at h

/-! ## §1. Single sweep: `fillCover` is false at `(2, 1, 1)` for every `gen` with `gen.1 ≤ 1` -/

/-- The old shell at `i = 2`, `ε = 1` contains `(4, 0)`. -/
theorem four_zero_mem_shell :
    ((4 : ℤ), (0 : ℤ)) ∈ MaxEnv.shell (Ai 2) ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 1 :=
  ⟨(4, 2), by simp only [Ai, mem_hexShape]; omega, 2, by ext <;> simp, by simp [dot]⟩

/-- `(4, 0) ∉ Ai 2`: `x - y = 4 > 2`. -/
theorem four_zero_not_mem_Ai : ((4 : ℤ), (0 : ℤ)) ∉ Ai 2 := by
  simp [Ai, mem_hexShape]

/-- The invariant: `x ≤ 3`, or already in `Ai 2`. -/
def Y : Set (ℤ × ℤ) := {z | z.1 ≤ 3} ∪ Ai 2

theorem Y_closed {gen : ℤ × ℤ} (hgen : gen.1 ≤ 1) (t : ℤ × ℤ)
    (h : ∀ b ∈ hexF.erase gen, b + t ∈ Y) : gen + t ∈ Y := by
  have h21 := h _ (mem_hexF_two_one hgen)
  left
  rcases h21 with h21 | h21
  · simp only [Set.mem_ofPred_eq, Prod.fst_add] at h21 ⊢; omega
  · simp only [Ai, mem_hexShape, Prod.fst_add, Prod.snd_add] at h21
    simp only [Set.mem_ofPred_eq, Prod.fst_add]; omega

theorem X_subset_Y :
    Ai 2 ∪ MaxEnv.shell (Ai 1) ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 1 ⊆ Y := by
  rintro z (hz | ⟨g, hg, t, rfl, -⟩)
  · exact Or.inr hz
  · left
    simp only [Ai, mem_hexShape] at hg
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.smul_fst, smul_eq_mul]; omega

/-- **`fillCover` is false for the single-sweep shell at `(i, i₀, ε) = (2, 1, 1)`**, for any
generating point with `gen.1 ≤ 1` (both bottom-face points `(0,0)`, `(1,0)` of `hexA`). -/
theorem not_fillCover_singleSweep {gen : ℤ × ℤ} (hgen : gen.1 ≤ 1) :
    ¬ MaxEnv.shell (Ai 2) ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 1 ⊆
      ⋃ n, genFill hexF gen
        (Ai 2 ∪ MaxEnv.shell (Ai 1) ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 1) n := by
  intro hsub
  have hY : ((4 : ℤ), (0 : ℤ)) ∈ Y :=
    genClosure_subset_of_closed X_subset_Y (Y_closed hgen) (hsub four_zero_mem_shell)
  rcases hY with h | h
  · simp at h
  · exact four_zero_not_mem_Ai h

theorem not_fillCover_singleSweep_gen00 :
    ¬ MaxEnv.shell (Ai 2) ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 1 ⊆
      ⋃ n, genFill hexF ((0 : ℤ), (0 : ℤ))
        (Ai 2 ∪ MaxEnv.shell (Ai 1) ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 1) n :=
  not_fillCover_singleSweep (by norm_num)

theorem not_fillCover_singleSweep_gen10 :
    ¬ MaxEnv.shell (Ai 2) ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 1 ⊆
      ⋃ n, genFill hexF ((1 : ℤ), (0 : ℤ))
        (Ai 2 ∪ MaxEnv.shell (Ai 1) ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 1) n :=
  not_fillCover_singleSweep (by norm_num)

/-! ## §2. `:518` object: `fillCover` holds at `(2, 1, 1)` for `gen = (1,0)`, fails for `(0,0)` -/

/-- Abbreviation for the `:518` shell on `ShellSweep`'s data. -/
def sh518 (i ε : ℕ) : Set (ℤ × ℤ) :=
  ShellMink.shellInter (Ai i)
    (MaxEnv.shell quad ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ε) ((-1 : ℤ), (-1 : ℤ))

theorem sh518_eq (i ε : ℕ) : sh518 i ε = hexShape (2 * i) (2 * i) i i ε :=
  shell518_eq_hexShape i ε

/-- **`fillCover` on the `:518` object at `(2, 1, 1)`, `gen = (1, 0)`.** -/
theorem fillCover_518_gen10 :
    sh518 2 1 ⊆ ⋃ n, genFill hexF ((1 : ℤ), (0 : ℤ)) (Ai 2 ∪ sh518 1 1) n := by
  change sh518 2 1 ⊆ genClosure hexF ((1 : ℤ), (0 : ℤ)) (Ai 2 ∪ sh518 1 1)
  refine subset_genClosure_of_rank (fun _ => 0) ?_
  intro z hz
  rw [sh518_eq] at hz
  obtain ⟨x, y⟩ := z
  simp only [mem_hexShape] at hz
  by_cases hA : ((x, y) : ℤ × ℤ) ∈ Ai 2
  · exact Or.inl (Or.inl hA)
  · simp only [Ai, mem_hexShape] at hA
    -- the only site of `Â_2^{(1)}` outside `Ai 2` is `(1, -1)` (and `(0,-1)`, which is in `Â_1^{(1)}`)
    have hy : y = -1 := by omega
    subst hy
    have hx : x = 0 ∨ x = 1 := by omega
    rcases hx with rfl | rfl
    · left; right; rw [sh518_eq]; simp only [mem_hexShape]; omega
    · right
      refine ⟨(0, -1), by ext <;> simp, ?_⟩
      intro b hb
      left
      obtain ⟨hne, hb'⟩ := Finset.mem_erase.1 hb
      simp only [hexF, Finset.mem_insert, Finset.mem_singleton] at hb'
      rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · right; rw [sh518_eq]; simp only [mem_hexShape]; norm_num
      · exact absurd rfl hne
      · left; simp only [Ai, mem_hexShape]; norm_num
      · left; simp only [Ai, mem_hexShape]; norm_num
      · left; simp only [Ai, mem_hexShape]; norm_num
      · left; simp only [Ai, mem_hexShape]; norm_num
      · left; simp only [Ai, mem_hexShape]; norm_num

/-- Invariant for `gen = (0,0)` on the `:518` data: `y ≥ 0`, or `x ≤ 0`. -/
def Y' : Set (ℤ × ℤ) := {z | 0 ≤ z.2 ∨ z.1 ≤ 0}

theorem Y'_closed (t : ℤ × ℤ)
    (h : ∀ b ∈ hexF.erase ((0 : ℤ), (0 : ℤ)), b + t ∈ Y') : ((0 : ℤ), (0 : ℤ)) + t ∈ Y' := by
  have h10 := h ((1 : ℤ), (0 : ℤ)) (by simp [hexF])
  simp only [Y', Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add] at h10 ⊢
  omega

/-- **`fillCover` on the `:518` object at `(2, 1, 1)` is false for `gen = (0, 0)`**: `(1,-1)`
would need `(2,-1)`, which lies outside `Â_2^{(1)}` (`x - y = 3`). -/
theorem not_fillCover_518_gen00 :
    ¬ sh518 2 1 ⊆ ⋃ n, genFill hexF ((0 : ℤ), (0 : ℤ)) (Ai 2 ∪ sh518 1 1) n := by
  intro hsub
  have hmem : ((1 : ℤ), (-1 : ℤ)) ∈ sh518 2 1 := by
    rw [sh518_eq]; simp only [mem_hexShape]; norm_num
  have hX : Ai 2 ∪ sh518 1 1 ⊆ Y' := by
    rintro z (hz | hz)
    · simp only [Ai, mem_hexShape] at hz; left; omega
    · rw [sh518_eq] at hz; simp only [mem_hexShape] at hz
      simp only [Y', Set.mem_ofPred_eq]; omega
  have := genClosure_subset_of_closed hX Y'_closed (hsub hmem)
  simp [Y'] at this

/-! ## §3. `shellSubStrip` re-proved on the `:518` object (`J = ι + 1` configuration) -/

/-- **`shellSubStrip` for the `:518` object** with `vl := (0,-1)`, `kk ≡ 0`, `B i := Ai i`:
`Â_i^{(ε)} ⊆ H_{Ai i}(ℓ)`.  Proved directly on the new object, not transported. -/
theorem shellSubStrip_518 (i ε : ℕ) :
    sh518 i ε ⊆ {z | z + ((0 : ℕ) : ℤ) • ((0 : ℤ), (-1 : ℤ)) ∈
      Colle35.halfStrip (Ai i) ((0 : ℤ), (-1 : ℤ))} := by
  intro z hz
  rw [sh518_eq] at hz
  obtain ⟨x, y⟩ := z
  simp only [mem_hexShape] at hz
  simp only [Set.mem_ofPred_eq, Nat.cast_zero, zero_smul, add_zero, Colle35.halfStrip]
  refine ⟨(x, max y 0), ?_, (max y 0 - y).toNat, ?_⟩
  · simp only [Ai, mem_hexShape]
    rcases le_or_gt 0 y with h | h
    · rw [max_eq_left h]; omega
    · rw [max_eq_right h.le]; omega
  · have ht : (((max y 0 - y).toNat : ℕ) : ℤ) = max y 0 - y :=
      Int.toNat_of_nonneg (by omega)
    ext <;> simp [ht]

/-! ## §4. The refuted binder, fed to the elaborator (PROTOCOL §27) -/

/-- `hatOf` with `kk ≡ 0` is the identity on the chain. -/
theorem hatOf_zero (v : ℤ × ℤ) (i : ℕ) : Colle35.hatOf Ai (fun _ => 0) v i = Ai i := by
  ext z; simp [Colle35.hatOf]

/-- **The `fillCover` binder of `ChainDataGeom.ofParts`, verbatim, at `ShellSweep`'s data with
`gen = (1,0)`, is false.**  The hypothesis is the binder's text with `A := Ai`, `kk := fun _ => 0`,
`vl := vJ1 := (0,-1)`, `nJ := (0,1)`, `cJ := 0`, `S := hexF`, `gen := (1,0)`; the elaborator,
not this docstring, certifies that it is the binder's shape. -/
theorem fillCover_binder_false
    (fillCover : ∀ i i₀ ε, MaxEnv.shell (Colle35.hatOf Ai (fun _ => 0) ((0 : ℤ), (-1 : ℤ)) i)
        ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ε ⊆
      ⋃ n, genFill hexF ((1 : ℤ), (0 : ℤ)) (Colle35.hatOf Ai (fun _ => 0) ((0 : ℤ), (-1 : ℤ)) i ∪
        MaxEnv.shell (Colle35.hatOf Ai (fun _ => 0) ((0 : ℤ), (-1 : ℤ)) i₀)
          ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ε) n) : False := by
  have h := fillCover 2 1 1
  simp only [hatOf_zero] at h
  exact not_fillCover_singleSweep_gen10 h

/-- Same, for `gen = (0,0)`. -/
theorem fillCover_binder_false_gen00
    (fillCover : ∀ i i₀ ε, MaxEnv.shell (Colle35.hatOf Ai (fun _ => 0) ((0 : ℤ), (-1 : ℤ)) i)
        ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ε ⊆
      ⋃ n, genFill hexF ((0 : ℤ), (0 : ℤ)) (Colle35.hatOf Ai (fun _ => 0) ((0 : ℤ), (-1 : ℤ)) i ∪
        MaxEnv.shell (Colle35.hatOf Ai (fun _ => 0) ((0 : ℤ), (-1 : ℤ)) i₀)
          ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ε) n) : False := by
  have h := fillCover 2 1 1
  simp only [hatOf_zero] at h
  exact not_fillCover_singleSweep_gen00 h

/-! ## §5. 守卫辨识：§1 的反例够不到**迁移后**的字段，够到的是 `shellEnv`

lane-leafa-gen，2026-09-25（PROTOCOL §26 / §103 / §108）。

本文件开头「Which signature's closure is refuted」那段（`:17-20`）写明 §1 反驳的是
**`ChainDataGeom.ofParts`** 的 `fillCover` binder，即 2026-09-19 那版的**无守卫**形。
2026-09-25 的 (B) 栈迁移之后，链上的字段换成了带守卫的

  `fillCover : ∀ ε i₀, 0 < ε → (∀ i, i₀ ≤ i → EnvOf ↑S (shellInter …)) → ∀ i, max i₀ I₀ ≤ i → …`

（`ChainPartsFeed.lean:271-279` ＝ `ofPartsInter` 的同名 binder，`ChainAssembleInter.lean:214-221`）。

⛔ **第 227 轮裁决 `w := vJ1` 时给的合成（`ShellMink.shellInter_vJ1_eq` ＋
`not_fillCover_singleSweep` ⟹ `fillCover` 为假）对这个带守卫的字段不成立**：本节证明，
在 §1 反例所用的同一组数据上取 `w := vJ1 = (0,-1)`，那条 `EnvOf` 守卫
**对一切 `ε`、一切 `i` 都为假**，于是字段是**空真**的（`fillCover_field_vacuous_at_vJ1`），
反例咬不到它。机理：塌成的单次 sweep 丢了 `(1,-1)` 那条边（`Nondeg` 的
`1 ≤ a - d + e` 在 `d = 2i + ε` 处恰好破），`E` 只剩 5 个法向，兑现不了 `Enveloped` 的
`(E T).encard = (E ↑hexF).encard`。

✅ **但裁决本身站得住，死的是另一个字段**：同一条 `not_envOf_shell_Ai` 直接否掉 `shellEnv`
（`ChainPartsFeed.lean:265-267`，`∃ ε i₀, 0 < ε ∧ ∀ i ≥ i₀, EnvOf …`）——
见 `not_shellEnv_field_at_vJ1`。`w := vJ1` 死在 `shellEnv` 上，不是死在 `fillCover` 上。

⚠ 辖域（PROTOCOL §54）：以上都是 `Ai` / `hexF` 这一组数据上的话。两种用法都合法：
否掉一条反驳只需指出该反驳自带的台架破了自己要用的守卫；给出一条反驳，因为 `shellEnv`
是 `∃ ε i₀`，台架上对一切 `ε i₀` 为假就是该台架上字段为假。不主张一般构型。
外层壳 `⋃ k, Ai k` 与 `quad` 由 `iUnion_Ai_eq_quad` 钉成同一集合，所以 §5 的负面与
`envOf_shell518_transverse` 的正面是**同一台架**上的对照（PROTOCOL §102）。 -/

/-- `w := vJ1 = (0,-1)` 时 `:518` 的交集对象塌成的那个集合（＝单次 sweep）。 -/
def sweepAi (i ε : ℕ) : Set (ℤ × ℤ) :=
  MaxEnv.shell (Ai i) ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ε

/-- `sweepAi i ε` 的两条外围不等式：`x ≤ 2i` 由 `Â_i` 给（sweep 不动 `x`），
`-ε ≤ y` 由壳的切割给。 -/
theorem mem_sweepAi_bounds {i ε : ℕ} {z : ℤ × ℤ} (hz : z ∈ sweepAi i ε) :
    z.1 ≤ 2 * (i : ℤ) ∧ -(ε : ℤ) ≤ z.2 := by
  obtain ⟨g, hg, t, rfl, hd⟩ := hz
  simp only [Ai, mem_hexShape] at hg
  simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hd ⊢
  omega

/-- `(2i, -ε) ∈ sweepAi i ε`：从 `(2i, i) ∈ Â_i` 向下扫 `i + ε` 步。 -/
theorem max_pt_mem_sweepAi (i ε : ℕ) : (2 * (i : ℤ), -(ε : ℤ)) ∈ sweepAi i ε := by
  refine ⟨(2 * (i : ℤ), (i : ℤ)), ?_, i + ε, ?_, ?_⟩
  · simp only [Ai, mem_hexShape]; omega
  · ext <;> simp
  · simp [dot]

/-- **`(1,-1)` 的暴露面是单点 `(2i, -ε)`**：`x - y` 在 `sweepAi i ε` 上的最大值 `2i + ε`
只在 `x = 2i`、`y = -ε` 处取到。这就是「丢了一条边」的内核形。 -/
theorem face_sweepAi_oneNegOne (i ε : ℕ) :
    face (sweepAi i ε) ((1 : ℤ), (-1 : ℤ)) = {(2 * (i : ℤ), -(ε : ℤ))} := by
  have hle : ∀ z ∈ sweepAi i ε, dot ((1 : ℤ), (-1 : ℤ)) z ≤ 2 * (i : ℤ) + (ε : ℤ) := by
    intro z hz
    obtain ⟨h1, h2⟩ := mem_sweepAi_bounds hz
    simp only [dot]; omega
  have hmem : ∃ z ∈ sweepAi i ε, dot ((1 : ℤ), (-1 : ℤ)) z = 2 * (i : ℤ) + (ε : ℤ) :=
    ⟨_, max_pt_mem_sweepAi i ε, by simp [dot]⟩
  rw [face_eq_of_support hle hmem]
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hzT, hzd⟩
    obtain ⟨h1, h2⟩ := mem_sweepAi_bounds hzT
    simp only [dot] at hzd
    have hxy : z.1 = 2 * (i : ℤ) ∧ z.2 = -(ε : ℤ) := by omega
    exact Prod.ext hxy.1 hxy.2
  · rintro rfl
    exact ⟨max_pt_mem_sweepAi i ε, by simp [dot]⟩

/-- `(1,-1)` 不是 `sweepAi i ε` 的边法向：面是单点，不是 `Nontrivial`。 -/
theorem not_isEdge_sweepAi_oneNegOne (i ε : ℕ) : ((1 : ℤ), (-1 : ℤ)) ∉ E (sweepAi i ε) := by
  rintro ⟨-, hnt⟩
  rw [face_sweepAi_oneNegOne] at hnt
  exact Set.not_nontrivial_singleton hnt

theorem oneNegOne_mem_E_hexF : ((1 : ℤ), (-1 : ℤ)) ∈ E (↑hexF : Set (ℤ × ℤ)) := by
  rw [coe_hexF, E_hexA_eq]
  simp only [hexE, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem finite_E_hexF : (E (↑hexF : Set (ℤ × ℤ))).Finite := by
  rw [coe_hexF, E_hexA_eq, hexE]
  repeat' apply Set.Finite.insert
  exact Set.finite_singleton _

/-- **单次 sweep 兑现不了 `EnvOf ↑hexF`**，对一切 `i`、一切 `ε`：`E` 少了 `(1,-1)`，
而 `Enveloped` 要求 `(E T).encard = (E ↑hexF).encard`。 -/
theorem not_envOf_shell_Ai (i ε : ℕ) : ¬ EnvOf (↑hexF : Set (ℤ × ℤ)) (sweepAi i ε) := by
  intro h
  have hss : E (sweepAi i ε) ⊂ E (↑hexF : Set (ℤ × ℤ)) :=
    ⟨h.1.E_subset, fun hsup => not_isEdge_sweepAi_oneNegOne i ε (hsup oneNegOne_mem_E_hexF)⟩
  exact absurd h.2 (ne_of_lt ((finite_E_hexF.subset h.1.E_subset).encard_lt_encard hss))

/-- `ShellMink.shellInter_shell_eq` 在本台架上的实例：`w := vJ1 := (0,-1)`。 -/
theorem shellInter_vJ1_eq_sweepAi (i ε : ℕ) :
    ShellMink.shellInter (Ai i)
        (MaxEnv.shell (⋃ k, Ai k) ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ε)
        ((0 : ℤ), (-1 : ℤ)) = sweepAi i ε :=
  ShellMink.shellInter_shell_eq (Set.subset_iUnion Ai i) _ _ _ _

/-- **迁移后的 `fillCover` 字段（`ChainPartsFeed.lean:271-279`）在 `w := vJ1` 处、本台架上
对一切 `I₀` 成立**，因为它的 `EnvOf` 守卫恒假。
⟹ `not_fillCover_singleSweep` 反驳不了它；第 227 轮那条合成只对 `ofParts` 的无守卫形有效。 -/
theorem fillCover_field_vacuous_at_vJ1 (I₀ : ℕ) (S : Finset (ℤ × ℤ))
    (hS : (↑S : Set (ℤ × ℤ)) = (↑hexF : Set (ℤ × ℤ))) (_gen : ℤ × ℤ) :
    ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ))
        (ShellMink.shellInter (Ai i)
          (MaxEnv.shell (⋃ k, Ai k) ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ε)
          ((0 : ℤ), (-1 : ℤ)))) →
      ∀ i, max i₀ I₀ ≤ i →
      ShellMink.shellInter (Ai i)
          (MaxEnv.shell (⋃ k, Ai k) ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ε)
          ((0 : ℤ), (-1 : ℤ)) ⊆
        {z | Colle37.GenClosure S (Ai i ∪
          ShellMink.shellInter (Ai i₀)
            (MaxEnv.shell (⋃ k, Ai k) ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ε)
            ((0 : ℤ), (-1 : ℤ))) z} := by
  intro ε i₀ hε hEnv i hi
  refine absurd (hEnv i (le_trans (le_max_left _ _) hi)) ?_
  rw [hS, shellInter_vJ1_eq_sweepAi]
  exact not_envOf_shell_Ai i ε

/-- **`shellEnv` 字段（`ChainPartsFeed.lean:265-267`）在 `w := vJ1` 处、本台架上为假。**
`shellEnv` 是 `∃ ε i₀`，而守卫对一切 `ε i₀ i` 都假 ⟹ 存在量词无处可取。
这是 `w := vJ1` 真正死掉的那一格，也是第 227 轮裁决应当引的那一条。 -/
theorem not_shellEnv_field_at_vJ1 (S : Finset (ℤ × ℤ))
    (hS : (↑S : Set (ℤ × ℤ)) = (↑hexF : Set (ℤ × ℤ))) :
    ¬ ∃ ε i₀ : ℕ, 0 < ε ∧
      ∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ))
        (ShellMink.shellInter (Ai i)
          (MaxEnv.shell (⋃ k, Ai k) ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ε)
          ((0 : ℤ), (-1 : ℤ))) := by
  rintro ⟨ε, i₀, -, hEnv⟩
  refine absurd (hEnv i₀ (le_refl i₀)) ?_
  rw [hS, shellInter_vJ1_eq_sweepAi]
  exact not_envOf_shell_Ai i₀ ε

/-- **台架的分母：字段里的 `⋃ i, Â_i` 就是 `quad`。**  取 `k := max x y`。 -/
theorem iUnion_Ai_eq_quad : (⋃ k, Ai k) = quad := by
  ext z
  simp only [Set.mem_iUnion, Ai, mem_hexShape, quad, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, h1, -, h3, -, -, -⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(max z.1 z.2).toNat, ?_⟩
    have ht : ((max z.1 z.2).toNat : ℤ) = max z.1 z.2 :=
      Int.toNat_of_nonneg (le_trans h1 (le_max_left _ _))
    rw [ht]
    refine ⟨h1, by omega, h2, by omega, by omega, by omega⟩

/-- **同一台架、同一 `ε`，横截方向 `w := -v_{ℓ_{J+1}} = (-1,-1)` 的守卫成立**
（`ShellSweep.enveloped_shell518_hexA`，`i ≥ ε + 1`），外层壳写成字段里的 `⋃ k, Â_k`。
与 `not_shellEnv_field_at_vJ1` 合起来说明：交集**不是**「the same set / 换栈没帮忙」，
它恰恰是 `shellEnv` 在本台架上活下来的唯一原因。 -/
theorem envOf_shell518_transverse {i ε : ℕ} (hi : ε + 1 ≤ i) :
    EnvOf (↑hexF : Set (ℤ × ℤ)) (ShellMink.shellInter (Ai i)
      (MaxEnv.shell (⋃ k, Ai k) ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ε)
      ((-1 : ℤ), (-1 : ℤ))) := by
  rw [coe_hexF, iUnion_Ai_eq_quad]
  exact enveloped_shell518_hexA hi

/-- **本台架上两个 `w` 取法的鉴别维度就是 `det vl w`**（PROTOCOL §84：报「判据通过」要同时
报它在哪个维度上有鉴别力）。台架的 `vl = vJ1 = (0,-1)`（`J = ι+1` 共线构型，`det vl vJ1 = 0`），
所以 `w := vJ1` 恰好实现 `det vl w = 0`，横截的 `w = (-1,-1)` 实现 `det vl w = -1 ≠ 0`。
配 `not_shellEnv_field_at_vJ1` / `envOf_shell518_transverse`：本台架上 `shellEnv`
成立与否与 `det vl w` 是否为零**同步翻转**。

⚠ 这只是台架（PROTOCOL §54）：它说明 `det vl w ≠ 0` 是**生产者必须自己保证**的一条，
而 `ChainDataGeomParts` 对 `w` 只有 `hsweepW : dot nJ w < 0`（`ChainPartsFeed.lean:239`），
**没有** `det vl w ≠ 0` 这个字段。不主张一般构型下 `shellEnv ⟺ det vl w ≠ 0`。

⛔ **2026-09-25 续测（§6）：上面那句「不主张」现在有了答案，是「不成立」。**
方窗口上 `det vl w = 0` 而 `shellEnv` **为真**（`shellEnv_field_at_vJ1_square`），
所以本条刻画的「同步翻转」只是 `hexF` 台架的现象，**不是** `det vl w` 在做功。
真正的鉴别维度见 §6 的 `hexF_rising_normal` / `sqF_no_rising_normal`。本条保留，
但凡引用它推一般结论的地方都要改引 §6。 -/
theorem det_vl_w_discriminates :
    Nivat.det ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) = 0 ∧
    Nivat.det ((0 : ℤ), (-1 : ℤ)) ((-1 : ℤ), (-1 : ℤ)) ≠ 0 := by
  refine ⟨by simp [Nivat.det], ?_⟩
  simp [Nivat.det]

/-! ## §6. 集成者第 228 轮派的问题：`shellEnv ⟹ det vl w ≠ 0` 成不成立？

**答案：不成立 —— `det vl w ≠ 0` 不能从 `shellEnv` 推出来，字段必须留着。**
证伪台架是**方窗口**：`↑S := sq1 = box (0,0) (1,1)`，塔 `Â_i := box (0,0) (i+1,i+1)`，
`vl = vJ1 = w = (0,-1)`（故 `det vl w = 0`），`nJ = (0,1)`，`cJ = 0`。
`not_shellEnv_imp_det_ne_zero` 是内核见证。

### 为什么方窗口活下来而六边形窗口死掉（机制，一般构型下也成立）

`E_shell_eq_of_shellEnv_at_vJ1` 是这条路的一般形：取 `w := vl` 时
`ShellMink.shellInter_shell_eq`（`ShellMink.lean:589`）把 `:518` 的对象塌成单次 sweep，
于是 `LE2.Enveloped.E_eq`（`LatticeEdges.lean:1732`）逼出

    E (MaxEnv.shell (Â_i) vJ1 nJ cJ ε) = E ↑S      （对一切 i ≥ i₀）

**这个等式成不成立，只取决于 `E ↑S` 相对 sweep 方向 `vJ1` 的形状，与 `det vl w` 无关。**
sweep 把 `dot μ ·` 抬高的法向（`0 < dot μ vJ1`）里，只有 `-nJ` 那一条能被截线补回来；
其余那种法向会被抹掉，`E` 就少一条。判据两侧都在内核里：

| 窗口 | 有没有 `μ ∈ E ↑S`，`0 < dot μ vJ1` 且 `μ ≠ -nJ` | `shellEnv` at `w := vJ1` |
|---|---|---|
| `↑hexF`（六边形） | **有**：`μ = (1,-1)`，`hexF_rising_normal` | **假**，`not_shellEnv_field_at_vJ1` |
| `↑sqF`（方形） | **没有**：`sqF_no_rising_normal` | **真**，`shellEnv_field_at_vJ1_square` |

分母 2/2，两个台架同一个外层 `⋃ Â_i = quad`（`iUnion_Ai_eq_quad` / `iUnion_sqBx_eq_quad`），
所以 §5 的「`det vl w` 是鉴别维度」这句话按 PROTOCOL §103 就地降级：
`det_vl_w_discriminates` 在 `hexF` 台架上仍然为真（它说的是那个台架），
但**它刻画的不是机制** —— 机制是上面这张表的第二列。

### 辖域：被证伪的是哪一版蕴含式（PROTOCOL §50）

`not_shellEnv_imp_det_ne_zero` 的前提表逐字列在它自己的语句里，共 16 条，全部是
`ChainDataGeomParts`（`ChainPartsFeed.lean:210` 起）里对 `w` / `vl` / `vJ1` / `nJ` / `S` / `Â`
有约束力的那些：`Primitive` 四条、`vJ1 = vl`（第 226 轮共线裁决）、`det vl vJ1 = 0`、
`dot nJ vJ1 = -1`（hbase 的强形，比字段 `hsweep` 强）、`hsweepW`（`:239`）、`hswept`、
`hfin`、`ahat_nonempty`、格凸、`AhatMono`、`hhp`、`envB`-形的 `Enveloped ↑S Â_i`、
`PosArea ↑S`、`(E ↑S).Finite`。

⛔ **未进前提表的字段**（所以本条**没有**证明「不存在任何推导」，只证明了「任何推导都必须用到
这张表之外的东西」）：`envShift` / `envB`（原形，走 `B i` 不走 `Â_i`）/ `maxA` / `subBA` /
`subAB` / `escapeW` / `shellSubStrip` / `fillCover` / `vJ` / `F : FaceBlock S nJ vJ` /
`gen_eq` / `bottom` / `rec_p` / `dot_nJ_p` / `ahat_halfPlane_L`。
其中 `bottom` 与 `F` 我在这座方形台架上**手算过**一个实例（`vJ := (1,0)`、`z₀ := (0,-ε-1)`、
`L := 0`；~~`sq1` 在 `nJ = (0,1)` 方向的面是 `{(0,1),(1,1)}`~~，方向正是 `(1,0)`），
⚠ **没有进内核**，按 PROTOCOL §51 不作为主张；其余各条我没算。

⚠ **第 248 轮订正（集成者，§14 划掉不删）：上面划掉的那半句方向错了，而且不是无害口误。**
`FaceBlock.lex`（`ANormal.lean:610`）逐字是
`∀ b ∈ S.erase a, dot (-n) b < dot (-n) a ∨ (dot (-n) b = dot (-n) a ∧ dot (-v) b < dot (-v) a)`,
即 `a` **最大化 `dot (-n)`、最小化 `dot n`**。在 `nJ = (0,1)` 上 `dot nJ b = b.2`，所以
`sq1 = box (0,0) (1,1)` 的那条面是 **`{(0,0),(1,0)}`**（`y` 最小那条），`a = (0,0)`
（`(0,0)` 与 `(1,0)` 在 `dot nJ` 上打平，由 `dot (-v)` 以 `v = (1,0)` 破平：需 `a.1 < b.1`）。
面的**方向**仍是 `(1,0)`，所以括号后半句不受影响；错的只是**面的位置**，而 `bottom` 的
第三合取（`∀ b ∈ S`，在 `k = L` 处）恰恰对 `F.a` 敏感 ⟹ 上面那个手算实例的数据要按
`a = (0,0)` 重算才能用。
由 lane-tower-hlev 报出、集成者按 `ANormal.lean:610` 原文复核确认；其内核见证是
`Nivat.TowerHlev2DFields.faceBlock_a_hex`（六边形窗口 `hexF` 上把同一约定钉成 `F.a = (0,0)`）。
本条只订正读法，不改本文件任何声明。

### 为什么我倾向于「一般构型下也推不出」，以及这不是主张

方形窗口不是人造的例外：`ChainDataGeomParts` 里**没有任何字段约束 `E ↑S` 的大小或形状**
——这是集成者自己第 200 轮逐字段点过的结果（`ChainPartsFeed.lean:218` 的结构：
**37** 个字段，`hEU` / `hES` / `hexE` **0 命中**）。⚠ 第 246 轮订正：此处原记
「34 个字段＝ 10 数据 ＋ 24 `Prop`」，且行号 `:167-176` 指的是一段散文而非结构本身；
唯一作数的字段数口径是内核 `getStructureFields`（`ChainPartsFeed.lean:189-197`，实跑 **37**）。
三条 `0 命中`的结论不受影响。而上面那张表说明机制**只**看
`E ↑S`。⚠ 这是「我没找到能排除方窗口的前提」，按 PROTOCOL §51 **不是**「不存在这种前提」。
真要消掉 `det vl w ≠ 0` 这笔硬规矩 5 的债，该找的不是它的证明，而是链上哪条字段蕴含
「`E ↑S` 有一条被 `vJ1` 抬高、又不是 `-nJ` 的法向」。 -/

/-- `hatOf` 的 `kk ≡ 0` 特例，对任意塔（`hatOf_zero` 只对 `Ai` 陈述）。 -/
theorem hatOf_zero_gen (A : ℕ → Set (ℤ × ℤ)) (v : ℤ × ℤ) (i : ℕ) :
    Colle35.hatOf A (fun _ => 0) v i = A i := by
  ext z; simp [Colle35.hatOf]

/-- 方窗口 `sq1 = box (0,0) (1,1)`（`LatticeEdges.lean:2074`）的 `Finset` 形。 -/
def sqF : Finset (ℤ × ℤ) :=
  {((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ)), ((1 : ℤ), (1 : ℤ))}

theorem coe_sqF : (↑sqF : Set (ℤ × ℤ)) = sq1 := by
  ext ⟨x, y⟩
  simp only [sqF, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, Prod.mk.injEq, sq1, mem_box]
  omega

/-- ⭐ **任何 `FaceBlock sqF (0,1) (1,0)` 的 `a` 只能是 `(0,0)`**（lane-leafa-gen，2026-09-26）。

**补的是哪个洞**：上面 §5 那条订正（「第 248 轮订正」段）已按 `ANormal.lean:610` 把读法改对,
但它列的内核见证是 `Nivat.TowerHlev2DFields.faceBlock_a_hex`，那条钉的是**六边形**窗口 `hexF`;
对**本文件的方窗口 `sqF`** 当时还只是同一约定下的算术推断（报出方 lane-tower-hlev 自己标为
未进内核）。下面两条把 `sqF` 这一侧也送进内核。

依据同上：`FaceBlock.lex` 要求 `a` 最大化 `dot (-n)` ⟺ **最小化** `dot n`；`n = (0,1)` ⟹
`dot n z = z.2` ⟹ `a` 取 `y` **最小**那条面。并列时 `dot (-v) b < dot (-v) a` ⟺
`dot v a < dot v b` ⟹ `a` 最小化 `dot v`，`v = (1,0)` ⟹ `x` 最小。⟹ 面是 `{(0,0),(1,0)}`。

⚠ **对 §5 那条订正的一处补充**：那里说手算实例「要按 `a = (0,0)` 重算才能用」。就 `F.a`
这一项而言，订正后的值**本来就是**该段其余数据所逼出的：该段取 `cJ = 0`、`z₀ = (0,-ε-1)`
（`dot nJ z₀ = -ε-1 = cJ-ε-1` ✓），而 `hhp` 要 `Â_i ⊆ {z | 0 ≤ z.2}`，支撑线即 `y = 0`,
面必须落在 `y = 0` 上；原先写的 `{(0,1),(1,1)}` 在 `y = 1`，本就与同段的 `cJ = 0` 矛盾。
⟹ 订正是让那段自洽，不是换掉一组数据。⛔ 但 `bottom` 的第三合取仍然**没有**进内核,
§51 的限定不变；上面这句只管 `F.a`，不管 `bottom`。

证法：对 `F.a_mem` 的四个点分情形；`a ≠ (0,0)` 时把 `F.lex` 代在 `b = (0,0)` 上,
两支分别要 `a.2 < 0` 与 `a.2 = 0 ∧ a.1 < 0`，在 `sqF` 上都不可能。 -/
theorem faceBlock_a_sqF (F : Colle35.FaceBlock sqF ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ))) :
    F.a = ((0 : ℤ), (0 : ℤ)) := by
  by_contra hne
  have hmem := F.a_mem
  have h0 : ((0 : ℤ), (0 : ℤ)) ∈ sqF.erase F.a := by
    refine Finset.mem_erase.mpr ⟨fun h => hne h.symm, ?_⟩
    simp [sqF]
  have hlex := F.lex _ h0
  simp only [sqF, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h <;> rw [h] at hlex <;> simp [dot] at hlex

/-- **同一条的 `a'` 一半**：`a' = (1,0)`。经 `F.lex'` 代在 `b = (1,0)` 上。 -/
theorem faceBlock_a'_sqF (F : Colle35.FaceBlock sqF ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ))) :
    F.a' = ((1 : ℤ), (0 : ℤ)) := by
  by_contra hne
  have hmem := F.a'_mem
  have h0 : ((1 : ℤ), (0 : ℤ)) ∈ sqF.erase F.a' := by
    refine Finset.mem_erase.mpr ⟨fun h => hne h.symm, ?_⟩
    simp [sqF]
  have hlex := F.lex' _ h0
  simp only [sqF, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h <;> rw [h] at hlex <;> simp [dot] at hlex

/-- 方形塔 `Â_i := box (0,0) (i+1, i+1)`，对**一切** `i` 非退化（不需要 `1 ≤ i` 的守卫）。 -/
def sqBx (i : ℕ) : Set (ℤ × ℤ) := box ((0 : ℤ), (0 : ℤ)) ((i : ℤ) + 1, (i : ℤ) + 1)

theorem mem_sqBx {i : ℕ} {z : ℤ × ℤ} :
    z ∈ sqBx i ↔ 0 ≤ z.1 ∧ z.1 ≤ (i : ℤ) + 1 ∧ 0 ≤ z.2 ∧ z.2 ≤ (i : ℤ) + 1 := Iff.rfl

theorem sqBx_eq_Icc (i : ℕ) : sqBx i = Set.Icc ((0 : ℤ), (0 : ℤ)) ((i : ℤ) + 1, (i : ℤ) + 1) := by
  ext z
  simp only [mem_sqBx, Set.mem_Icc, Prod.le_def]
  tauto

theorem finite_sqBx (i : ℕ) : (sqBx i).Finite := by
  rw [sqBx_eq_Icc]; exact Set.finite_Icc _ _

theorem nonempty_sqBx (i : ℕ) : (sqBx i).Nonempty :=
  ⟨((0 : ℤ), (0 : ℤ)), by simp only [mem_sqBx]; omega⟩

theorem lc_sqBx (i : ℕ) : IsLatticeConvexRegion (sqBx i) := isLatticeConvexRegion_box _ _

theorem mono_sqBx (i j : ℕ) (hij : i ≤ j) : sqBx i ⊆ sqBx j := by
  intro z hz
  simp only [mem_sqBx] at hz ⊢
  omega

theorem hhp_sqBx (i : ℕ) : sqBx i ⊆ halfPlaneGE ((0 : ℤ), (1 : ℤ)) 0 := by
  intro z hz
  simp only [mem_sqBx] at hz
  simp only [halfPlaneGE, Set.mem_ofPred_eq, dot]
  omega

theorem env_sqBx (i : ℕ) : Enveloped (↑sqF : Set (ℤ × ℤ)) (sqBx i) := by
  rw [coe_sqF]
  refine envOf_sq1_box ?_ ?_
  · show (0 : ℤ) < (i : ℤ) + 1
    omega
  · show (0 : ℤ) < (i : ℤ) + 1
    omega

/-- **两座台架的分母是同一个**（PROTOCOL §102）：方形塔的 `⋃ i, Â_i` 也是 `quad`，
与 `iUnion_Ai_eq_quad` 对齐，所以正负两条收据不是在两个不同外层上比较。 -/
theorem iUnion_sqBx_eq_quad : (⋃ k, sqBx k) = quad := by
  ext z
  simp only [Set.mem_iUnion, mem_sqBx, quad, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, h1, -, h3, -⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(max z.1 z.2).toNat, ?_⟩
    have ht : ((max z.1 z.2).toNat : ℤ) = max z.1 z.2 :=
      Int.toNat_of_nonneg (le_trans h1 (le_max_left _ _))
    rw [ht]
    refine ⟨h1, by omega, h2, by omega⟩

/-- `hswept` 字段（`ChainPartsFeed.lean:221`）在方形台架上成立。 -/
theorem swept_sqBx :
    MaxEnv.SweptClosed (⋃ k, sqBx k) ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 := by
  intro g hg t hd
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hg
  simp only [mem_sqBx] at hk
  simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hd
  refine Set.mem_iUnion.mpr ⟨k, ?_⟩
  simp only [mem_sqBx, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  omega

/-- **单次 sweep 把方形扫成方形**：`MaxEnv.shell (box (0,0) (i+1,i+1)) (0,-1) (0,1) 0 ε
= box (0,-ε) (i+1,i+1)`。与 `sweepAi`（§5）的对照点就在这里 —— 那里的对象要写成
`hexShape` 才行，且 `Nondeg` 的右下不等式恰好破掉；这里根本没有对角边可破。 -/
theorem shell_sqBx_eq (i ε : ℕ) :
    MaxEnv.shell (sqBx i) ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ε
      = box ((0 : ℤ), -(ε : ℤ)) ((i : ℤ) + 1, (i : ℤ) + 1) := by
  ext z
  constructor
  · rintro ⟨g, hg, t, rfl, hd⟩
    simp only [mem_sqBx] at hg
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hd
    simp only [mem_box, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    omega
  · intro hz
    simp only [mem_box] at hz
    refine ⟨(z.1, max z.2 0), ?_, (max z.2 0 - z.2).toNat, ?_, ?_⟩
    · simp only [mem_sqBx]; omega
    · have ht : (((max z.2 0 - z.2).toNat : ℕ) : ℤ) = max z.2 0 - z.2 :=
        Int.toNat_of_nonneg (by omega)
      ext <;> simp [ht]
    · simp only [dot]; omega

/-- `:518` 的交集对象在 `w := vJ1` 处塌成单次 sweep，方形台架版（对照 §5 的
`shellInter_vJ1_eq_sweepAi`）。 -/
theorem shellInter_sqBx_vJ1_eq (i ε : ℕ) :
    ShellMink.shellInter (sqBx i)
        (MaxEnv.shell (⋃ k, sqBx k) ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ε)
        ((0 : ℤ), (-1 : ℤ))
      = box ((0 : ℤ), -(ε : ℤ)) ((i : ℤ) + 1, (i : ℤ) + 1) :=
  (ShellMink.shellInter_shell_eq (Set.subset_iUnion sqBx i) _ _ _ _).trans (shell_sqBx_eq i ε)

/-- **`shellEnv` 字段（`ChainPartsFeed.lean:265-267`）在 `w := vJ1` 处、方窗口上成立。**
取 `ε := 1`、`i₀ := 0`，对**一切** `i`（连守卫都不需要）。塔写成字段里的
`Colle35.hatOf A kk vl i` 形，`kk := fun _ => 0`，经 `hatOf_zero_gen`。

与 §5 的 `not_shellEnv_field_at_vJ1` 对读：同一个 `w`、同一个外层 `quad`、同一个 `det vl w = 0`，
`shellEnv` 一真一假 ⟹ `det vl w` 不是决定它的那个量。 -/
theorem shellEnv_field_at_vJ1_square :
    ∃ ε i₀ : ℕ, 0 < ε ∧
      ∀ i, i₀ ≤ i → EnvOf (↑sqF : Set (ℤ × ℤ))
        (ShellMink.shellInter (Colle35.hatOf sqBx (fun _ => 0) ((0 : ℤ), (-1 : ℤ)) i)
          (MaxEnv.shell (⋃ k, Colle35.hatOf sqBx (fun _ => 0) ((0 : ℤ), (-1 : ℤ)) k)
            ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ε)
          ((0 : ℤ), (-1 : ℤ))) := by
  refine ⟨1, 0, one_pos, fun i _ => ?_⟩
  simp only [hatOf_zero_gen]
  rw [coe_sqF, shellInter_sqBx_vJ1_eq]
  refine envOf_sq1_box ?_ ?_
  · show (0 : ℤ) < (i : ℤ) + 1
    omega
  · show -((1 : ℕ) : ℤ) < (i : ℤ) + 1
    simp only [Nat.cast_one]
    omega

/-- **本轮的答案：`det vl w ≠ 0` 不能从 `shellEnv` 推出来。**
16 条前提逐字列在语句里（见 §6 开头的辖域段），全部由方形台架兑现，而结论
`det vl w ≠ 0` 为假（`vl = w = (0,-1)`）。

⛔ 这条**不**证明「不存在任何推导」——它证明的是「任何推导都必须用到这 16 条之外的字段」，
未列入的字段清单见 §6 开头。 -/
theorem not_shellEnv_imp_det_ne_zero :
    ¬ (∀ (S : Finset (ℤ × ℤ)) (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (vl vJ1 nJ w : ℤ × ℤ) (cJ : ℤ),
        Primitive vl → Primitive vJ1 → Primitive nJ → Primitive w →
        vJ1 = vl → Nivat.det vl vJ1 = 0 →
        dot nJ vJ1 = -1 → dot nJ w < 0 →
        MaxEnv.SweptClosed (⋃ k, Colle35.hatOf A kk vl k) vJ1 nJ cJ →
        (∀ i, (Colle35.hatOf A kk vl i).Finite) →
        (∀ i, (Colle35.hatOf A kk vl i).Nonempty) →
        (∀ i, IsLatticeConvexRegion (Colle35.hatOf A kk vl i)) →
        (∀ i j, i ≤ j → Colle35.hatOf A kk vl i ⊆ Colle35.hatOf A kk vl j) →
        (∀ i, Colle35.hatOf A kk vl i ⊆ halfPlaneGE nJ cJ) →
        (∀ i, Enveloped (↑S : Set (ℤ × ℤ)) (Colle35.hatOf A kk vl i)) →
        PosArea (↑S : Set (ℤ × ℤ)) →
        (E (↑S : Set (ℤ × ℤ))).Finite →
        (∃ ε i₀ : ℕ, 0 < ε ∧
          ∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ))
            (ShellMink.shellInter (Colle35.hatOf A kk vl i)
              (MaxEnv.shell (⋃ k, Colle35.hatOf A kk vl k) vJ1 nJ cJ ε) w)) →
        Nivat.det vl w ≠ 0) := by
  intro h
  refine h sqF sqBx (fun _ => 0) ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ))
    ((0 : ℤ), (-1 : ℤ)) 0
    ⟨0, -1, by norm_num⟩ ⟨0, -1, by norm_num⟩ ⟨0, 1, by norm_num⟩ ⟨0, -1, by norm_num⟩
    rfl (by simp [Nivat.det]) (by simp [dot]) (by simp [dot])
    (by simp only [hatOf_zero_gen]; exact swept_sqBx)
    (fun i => by rw [hatOf_zero_gen]; exact finite_sqBx i)
    (fun i => by rw [hatOf_zero_gen]; exact nonempty_sqBx i)
    (fun i => by rw [hatOf_zero_gen]; exact lc_sqBx i)
    (fun i j hij => by rw [hatOf_zero_gen, hatOf_zero_gen]; exact mono_sqBx i j hij)
    (fun i => by rw [hatOf_zero_gen]; exact hhp_sqBx i)
    (fun i => by rw [hatOf_zero_gen]; exact env_sqBx i)
    (by rw [coe_sqF]; exact posArea_sq1) ?_ shellEnv_field_at_vJ1_square ?_
  · rw [coe_sqF, E_sq1]
    repeat' apply Set.Finite.insert
    exact Set.finite_singleton _
  · simp [Nivat.det]

/-- **`shellEnv` 在 `w := vl` 处到底逼出什么（一般构型，不是台架）。**
`ShellMink.shellInter_shell_eq`（`ShellMink.lean:589`）＋ `LE2.Enveloped.E_eq`
（`LatticeEdges.lean:1732`）：逼出的是「单次 sweep 的法向扇 = `E ↑S`」。
这是 `det vl w = 0` 这一格的**全部**内容；下面两条把它的成败归到 `E ↑S` 的形状上。

⚠ **非空真见证（§41／第 236 轮的「被假设」限定）**：`hEnv` 在本条里是**被假设**的位置，
Lean 不查它可不可满足 ⟹ 必须另配见证。见证是同文件 §6 的
`shellEnv_field_at_vJ1_square`（`S := sqF`、`Ahat := hatOf sqBx (fun _ => 0) (0,-1)`、
`v := (0,-1)`、`n := (0,1)`、`c := 0`、`ε := 1`、`i₀ := 0`），形状逐字对上本条的
`shellInter (Ahat i) (shell (⋃ k, Ahat k) v n c ε) v`（末位就是 `w := v`）。
⛔ 反过来在 `↑hexF` 上 `hEnv` **不可满足**（`not_shellEnv_field_at_vJ1`），
所以本条在六边形台架上是空真的 —— 引用时必须说清楚站在哪座台架上。 -/
theorem E_shell_eq_of_shellEnv_at_vJ1 {S : Finset (ℤ × ℤ)} {Ahat : ℕ → Set (ℤ × ℤ)}
    {v n : ℤ × ℤ} {c : ℤ} {ε i₀ : ℕ}
    (hSfin : (E (↑S : Set (ℤ × ℤ))).Finite)
    (hEnv : ∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ))
      (ShellMink.shellInter (Ahat i) (MaxEnv.shell (⋃ k, Ahat k) v n c ε) v)) :
    ∀ i, i₀ ≤ i → E (MaxEnv.shell (Ahat i) v n c ε) = E (↑S : Set (ℤ × ℤ)) := by
  intro i hi
  have h := hEnv i hi
  rw [ShellMink.shellInter_shell_eq (Set.subset_iUnion Ahat i)] at h
  exact Enveloped.E_eq hSfin h

/-- 判据的一侧：六边形窗口有一条被 sweep 抬高、又不是 `-nJ` 的法向，就是 `(1,-1)`；
`not_envOf_shell_Ai` 死在它上面。 -/
theorem hexF_rising_normal :
    ((1 : ℤ), (-1 : ℤ)) ∈ E (↑hexF : Set (ℤ × ℤ)) ∧
      0 < dot ((1 : ℤ), (-1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) ∧
      ((1 : ℤ), (-1 : ℤ)) ≠ ((0 : ℤ), (-1 : ℤ)) :=
  ⟨oneNegOne_mem_E_hexF, by simp [dot], by decide⟩

/-- 判据的另一侧：方窗口没有这种法向 —— 唯一被 sweep 抬高的就是 `-nJ = (0,-1)` 自己，
而那一条由截线 `cJ - ε ≤ dot nJ ·` 补回来。⟹ 鉴别维度是「`E ↑S` 相对 `vJ1`」，
**不是** `det vl w`。 -/
theorem sqF_no_rising_normal :
    ∀ μ ∈ E (↑sqF : Set (ℤ × ℤ)), 0 < dot μ ((0 : ℤ), (-1 : ℤ)) →
      μ = ((0 : ℤ), (-1 : ℤ)) := by
  intro μ hμ hpos
  rw [coe_sqF, E_sq1] at hμ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hμ
  rcases hμ with rfl | rfl | rfl | rfl
  · exact absurd hpos (by simp [dot])
  · exact absurd hpos (by simp [dot])
  · exact absurd hpos (by simp [dot])
  · rfl

/-! ## §8. `b3_colle2.txt:38` 的 `0 < i₀`：∃ 侧代价恒为零（lane-leafa-gen，第 234 轮）

**为什么要问这一问。** `b3_colle2.txt:38` 逐字写着
「We use $\mathbb{N}=\{1,2,\ldots\}$ and $\mathbb{Z}_{+}=\mathbb{N}\cup\{0\}$ .」，
而 `:520` 的 `i_0 \in \mathbb{N}` / `I_0 \in \mathbb{N}` 在 Lean 侧被转成含 `0` 的 `ℕ`
⟹ `ChainDataGeomParts` 的四条字段各比原文多一个实例（硬规矩 5：没有原文对应物的量词当场删）。
本节回答 ∃ 侧（`shellEnv`）删掉它要花多少钱。

**答案：零，而且是一般事实。** `exists_pos_i₀` 不吃几何、不吃台架，`P` 完全自由；
唯一用到的是守卫 `i₀ ≤ i` 对 `i₀` **反单调**，把 `i₀` 抬到 `i₀ + 1` 只让前件更难满足。
配上反向的 `exists_of_pos_i₀`，两个字段形状**等价** ⟹ 改 `shellEnv` 不改任何链上判断。

⚠ ∀ 侧（`shellSubStrip` / `fillCover`）**不是**这样：那边加前件会让反例失效，
见 `HwinRefute.lean` §9 的 `not_HwinI₀Pos_oct8`（实例必须从 `i := max I₀ 1` 改成
`max I₀ 1 + 1`）。⛔ 本节只覆盖 ∃ 侧，不要拿它当「这条修正是纯记账」的依据。 -/

/-- ⭐ **`∃ ε i₀, 0 < ε ∧ ∀ i ≥ i₀, P ε i` 自动升级成带 `0 < i₀` 的版本。**
取 `i₀ + 1`；`P` 自由，没有几何。 -/
theorem exists_pos_i₀ {P : ℕ → ℕ → Prop}
    (h : ∃ ε i₀ : ℕ, 0 < ε ∧ ∀ i, i₀ ≤ i → P ε i) :
    ∃ ε i₀ : ℕ, 0 < ε ∧ 0 < i₀ ∧ ∀ i, i₀ ≤ i → P ε i := by
  obtain ⟨ε, i₀, hε, hP⟩ := h
  exact ⟨ε, i₀ + 1, hε, Nat.succ_pos _, fun i hi => hP i (le_trans (Nat.le_succ i₀) hi)⟩

/-- 反向（丢掉那条合取）。与 `exists_pos_i₀` 合起来：∃ 侧两个字段形状等价。 -/
theorem exists_of_pos_i₀ {P : ℕ → ℕ → Prop}
    (h : ∃ ε i₀ : ℕ, 0 < ε ∧ 0 < i₀ ∧ ∀ i, i₀ ≤ i → P ε i) :
    ∃ ε i₀ : ℕ, 0 < ε ∧ ∀ i, i₀ ≤ i → P ε i := by
  obtain ⟨ε, i₀, hε, -, hP⟩ := h
  exact ⟨ε, i₀, hε, hP⟩

/-- **方窗口的 `shellEnv` 见证在 `0 < i₀` 下照样成立**，且是 `exists_pos_i₀` 的直接实例
（`shellEnv_field_at_vJ1_square` 原样喂进去，不重证）。 -/
theorem shellEnv_field_at_vJ1_square_pos :
    ∃ ε i₀ : ℕ, 0 < ε ∧ 0 < i₀ ∧
      ∀ i, i₀ ≤ i → EnvOf (↑sqF : Set (ℤ × ℤ))
        (ShellMink.shellInter (Colle35.hatOf sqBx (fun _ => 0) ((0 : ℤ), (-1 : ℤ)) i)
          (MaxEnv.shell (⋃ k, Colle35.hatOf sqBx (fun _ => 0) ((0 : ℤ), (-1 : ℤ)) k)
            ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ε)
          ((0 : ℤ), (-1 : ℤ))) :=
  exists_pos_i₀ shellEnv_field_at_vJ1_square

/-- **六边形窗口的 `shellEnv` 反例在 `0 < i₀` 下照样成立。**
`¬∃` 一侧加合取本来会变难否，这里不变：原证明在**任意** `i₀` 处取 `hEnv i₀ le_rfl`，
从不依赖 `i₀ = 0`。⟹ §6 的裁决（`det vl w ≠ 0` 推不出来）不受 `:38` 修正影响。 -/
theorem not_shellEnv_field_at_vJ1_pos (S : Finset (ℤ × ℤ))
    (hS : (↑S : Set (ℤ × ℤ)) = (↑hexF : Set (ℤ × ℤ))) :
    ¬ ∃ ε i₀ : ℕ, 0 < ε ∧ 0 < i₀ ∧
      ∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ))
        (ShellMink.shellInter (Ai i)
          (MaxEnv.shell (⋃ k, Ai k) ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ε)
          ((0 : ℤ), (-1 : ℤ))) :=
  fun h => not_shellEnv_field_at_vJ1 S hS (exists_of_pos_i₀ h)

/-- ⭐ **§6 的裁决在 `:38` 修正之后照样成立**（`0 < i₀` 版，第 236 轮 lane-leafa-gen）。

集成者已认下 `b3_colle2.txt:38`（`ℕ = {1,2,…}`）并**正在落 ∃ 侧**：`shellEnv` 字段改成
`∃ ε i₀, 0 < ε ∧ 0 < i₀ ∧ …`。§6 的 `not_shellEnv_imp_det_ne_zero` 前提表里写的是
**改之前**的 `shellEnv` 形状 ⟹ 字段一落，它说的就是一条链上不再存在的形状。
本条把那条裁决重述到现役形状上。

⚠ **这条不能从 §6 那条推出来，方向是反的**（env-refute 第 235 轮的 a fortiori 判据）：
`shellEnv_pos → shellEnv_old`（丢掉合取，`exists_of_pos_i₀`），于是
`(shellEnv_old → C) → (shellEnv_pos → C)`，取逆否得 **本条 ⟹ §6 那条**（见下面
`not_shellEnv_imp_det_ne_zero_of_pos`）。即：往**被否蕴含式的前件**里加合取，
否定变**强**，必须重证；重证的代价是把 `shellEnv_field_at_vJ1_square` 换成
`shellEnv_field_at_vJ1_square_pos`，其余 15 条前提一字未动。

⛔ 辖域与 §6 那条完全相同（16 条前提逐字在语句里，未进表的字段清单见 §6 开头）：
本条**不**证明「不存在任何推导」，只证明「任何推导都必须用到这 16 条之外的东西」。 -/
theorem not_shellEnv_imp_det_ne_zero_pos :
    ¬ (∀ (S : Finset (ℤ × ℤ)) (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (vl vJ1 nJ w : ℤ × ℤ) (cJ : ℤ),
        Primitive vl → Primitive vJ1 → Primitive nJ → Primitive w →
        vJ1 = vl → Nivat.det vl vJ1 = 0 →
        dot nJ vJ1 = -1 → dot nJ w < 0 →
        MaxEnv.SweptClosed (⋃ k, Colle35.hatOf A kk vl k) vJ1 nJ cJ →
        (∀ i, (Colle35.hatOf A kk vl i).Finite) →
        (∀ i, (Colle35.hatOf A kk vl i).Nonempty) →
        (∀ i, IsLatticeConvexRegion (Colle35.hatOf A kk vl i)) →
        (∀ i j, i ≤ j → Colle35.hatOf A kk vl i ⊆ Colle35.hatOf A kk vl j) →
        (∀ i, Colle35.hatOf A kk vl i ⊆ halfPlaneGE nJ cJ) →
        (∀ i, Enveloped (↑S : Set (ℤ × ℤ)) (Colle35.hatOf A kk vl i)) →
        PosArea (↑S : Set (ℤ × ℤ)) →
        (E (↑S : Set (ℤ × ℤ))).Finite →
        (∃ ε i₀ : ℕ, 0 < ε ∧ 0 < i₀ ∧
          ∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ))
            (ShellMink.shellInter (Colle35.hatOf A kk vl i)
              (MaxEnv.shell (⋃ k, Colle35.hatOf A kk vl k) vJ1 nJ cJ ε) w)) →
        Nivat.det vl w ≠ 0) := by
  intro h
  refine h sqF sqBx (fun _ => 0) ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ))
    ((0 : ℤ), (-1 : ℤ)) 0
    ⟨0, -1, by norm_num⟩ ⟨0, -1, by norm_num⟩ ⟨0, 1, by norm_num⟩ ⟨0, -1, by norm_num⟩
    rfl (by simp [Nivat.det]) (by simp [dot]) (by simp [dot])
    (by simp only [hatOf_zero_gen]; exact swept_sqBx)
    (fun i => by rw [hatOf_zero_gen]; exact finite_sqBx i)
    (fun i => by rw [hatOf_zero_gen]; exact nonempty_sqBx i)
    (fun i => by rw [hatOf_zero_gen]; exact lc_sqBx i)
    (fun i j hij => by rw [hatOf_zero_gen, hatOf_zero_gen]; exact mono_sqBx i j hij)
    (fun i => by rw [hatOf_zero_gen]; exact hhp_sqBx i)
    (fun i => by rw [hatOf_zero_gen]; exact env_sqBx i)
    (by rw [coe_sqF]; exact posArea_sq1) ?_ shellEnv_field_at_vJ1_square_pos ?_
  · rw [coe_sqF, E_sq1]
    repeat' apply Set.Finite.insert
    exact Set.finite_singleton _
  · simp [Nivat.det]

/-- 上面那条是**强**的：`:38` 修正前的 §6 版本是它的推论，不必再单独维护。
（`exists_of_pos_i₀` 把 `0 < i₀` 丢掉，前件变弱、蕴含式变强、否定变弱。） -/
theorem not_shellEnv_imp_det_ne_zero_of_pos :
    ¬ (∀ (S : Finset (ℤ × ℤ)) (A : ℕ → Set (ℤ × ℤ)) (kk : ℕ → ℕ) (vl vJ1 nJ w : ℤ × ℤ) (cJ : ℤ),
        Primitive vl → Primitive vJ1 → Primitive nJ → Primitive w →
        vJ1 = vl → Nivat.det vl vJ1 = 0 →
        dot nJ vJ1 = -1 → dot nJ w < 0 →
        MaxEnv.SweptClosed (⋃ k, Colle35.hatOf A kk vl k) vJ1 nJ cJ →
        (∀ i, (Colle35.hatOf A kk vl i).Finite) →
        (∀ i, (Colle35.hatOf A kk vl i).Nonempty) →
        (∀ i, IsLatticeConvexRegion (Colle35.hatOf A kk vl i)) →
        (∀ i j, i ≤ j → Colle35.hatOf A kk vl i ⊆ Colle35.hatOf A kk vl j) →
        (∀ i, Colle35.hatOf A kk vl i ⊆ halfPlaneGE nJ cJ) →
        (∀ i, Enveloped (↑S : Set (ℤ × ℤ)) (Colle35.hatOf A kk vl i)) →
        PosArea (↑S : Set (ℤ × ℤ)) →
        (E (↑S : Set (ℤ × ℤ))).Finite →
        (∃ ε i₀ : ℕ, 0 < ε ∧
          ∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ))
            (ShellMink.shellInter (Colle35.hatOf A kk vl i)
              (MaxEnv.shell (⋃ k, Colle35.hatOf A kk vl k) vJ1 nJ cJ ε) w)) →
        Nivat.det vl w ≠ 0) :=
  fun h => not_shellEnv_imp_det_ne_zero_pos fun S A kk vl vJ1 nJ w cJ p1 p2 p3 p4 e d dv dw
    sw fin ne lc mo hp env pa fe hshell =>
    h S A kk vl vJ1 nJ w cJ p1 p2 p3 p4 e d dv dw sw fin ne lc mo hp env pa fe
      (exists_of_pos_i₀ hshell)

/-! ## §9. `FillCoverStrip` 的正控：`:518` 台架上三格同时为真（lane-leafa-gen，第 234 轮）

集成者点头做 `hwin` 的逐量词对齐（上一轮已交，判定表在 `blueprint/LEAF-A.md`）。
按 §71，投证明力之前先测**前件可满足**与**结论非空真**。本节在 `:518` 六边形台架上
把两件一起测掉，用的全是本文件 §1–§3 现成的对象，不新造数据。

台架：`↑S := ↑hexF`、`Â_i := Ai i`、`vl = vJ1 = (0,-1)`、`w = (-1,-1)`（横截）、
`nJ = (0,1)`、`cJ = 0`、`kk ≡ 0`、`B i := Ai i`，`:518` 的对象是 `sh518 i ε`。

| `FillCoverStrip` 的那一格 | 原文 | 本台架上的收据 | 射程 |
|---|---|---|---|
| 守卫 | `:520` 右半 | `shellSubStrip_518` | 对**一切** `i ε` |
| 包络 | `shellEnv` 的前件 | `envOf_shell518_transverse` | `i ≥ ε + 1` |
| 残项 | `:528`/`:530` | `genClosure_518` | 只在 `(i,i₀,ε) = (2,1,1)` |

⚠ 残项那一格**不是全称的**，所以本节回答的是「投不投得起」，**不是**「定理真不真」（§71）。

⚠ `fillCover_518_gen10` 是 `genFill hexF (1,0)` 形，而字段要的是**锚点无关**的
`Colle37.GenClosure`（`GenClosureDef.lean`：`step` 对任意 `a ∈ S` 且 `LatticeConvex (S.erase a)`
都开）。桥是 `GenClosureWeaken.genFill_subset_genClosure`，侧条件 `LatticeConvex (hexF.erase (1,0))`
全仓原先没有，本节补上。

⛔ **`not_fillCover_518_gen00` 不是字段的反例。**  同一台架、同一 `(2,1,1)`：`gen = (0,0)`
那一支为假，而锚点无关形为真（`gen00_false_but_genClosure_true` 把两半钉在一条语句里）。
⟹ 否掉的是**单锚点滤链** `genFill hexF (0,0)`，不是 `fillCover`。引用它必须带锚点（§54）。 -/

/-- `hexF.erase (1,0) = {(0,0),(0,1),(1,1),(1,2),(2,1),(2,2)}` 的实凸包所在的五条半平面
`0 ≤ x`、`x ≤ 2`、`y ≤ 2`、`y - x ≤ 1`、`x ≤ 2y`，其交在 `ℝ²` 里是凸的。 -/
theorem convex_pent :
    Convex ℝ {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 2 ∧ p.2 ≤ 2 ∧ p.2 - p.1 ≤ 1 ∧ p.1 ≤ 2 * p.2} := by
  rintro x ⟨hx1, hx2, hx3, hx4, hx5⟩ y ⟨hy1, hy2, hy3, hy4, hy5⟩ a b ha hb hab
  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- ⭐ **`LatticeConvex (hexF.erase (1,0))`** —— `genFill → GenClosure` 那座桥的侧条件。
证法与 `Colle37.latticeConvex_Sphi` 同款：`convexHull_min` 把实凸包压进半平面交，
再把五条实不等式转回 ℤ，`omega` 逐列穷举 `x = 0,1,2`。

⭐ 整性在 `x ≤ 2y` 这条上做功：`x = 1` 时实点可取 `y = 1/2`，整点必须 `y ≥ 1`
—— 这正是擦掉 `(1,0)` 之后剩下的集合仍然格凸的原因。 -/
theorem latticeConvex_hexF_erase10 : LatticeConvex (hexF.erase ((1 : ℤ), (0 : ℤ))) := by
  intro z hz
  have hsub : Conv (hexF.erase ((1 : ℤ), (0 : ℤ))) ⊆
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 2 ∧ p.2 ≤ 2 ∧ p.2 - p.1 ≤ 1 ∧ p.1 ≤ 2 * p.2} := by
    apply convexHull_min _ convex_pent
    rintro _ ⟨w, hw, rfl⟩
    rw [Finset.mem_coe, Finset.mem_erase] at hw
    obtain ⟨hne, hw⟩ := hw
    simp only [hexF, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by norm_num [toReal], by norm_num [toReal], by norm_num [toReal],
        by norm_num [toReal], by norm_num [toReal]⟩
    · exact absurd rfl hne
    · exact ⟨by norm_num [toReal], by norm_num [toReal], by norm_num [toReal],
        by norm_num [toReal], by norm_num [toReal]⟩
    · exact ⟨by norm_num [toReal], by norm_num [toReal], by norm_num [toReal],
        by norm_num [toReal], by norm_num [toReal]⟩
    · exact ⟨by norm_num [toReal], by norm_num [toReal], by norm_num [toReal],
        by norm_num [toReal], by norm_num [toReal]⟩
    · exact ⟨by norm_num [toReal], by norm_num [toReal], by norm_num [toReal],
        by norm_num [toReal], by norm_num [toReal]⟩
    · exact ⟨by norm_num [toReal], by norm_num [toReal], by norm_num [toReal],
        by norm_num [toReal], by norm_num [toReal]⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hsub hz
  simp only [toReal] at h1 h2 h3 h4 h5
  have e1 : (0 : ℤ) ≤ z.1 := by exact_mod_cast h1
  have e2 : z.1 ≤ 2 := by exact_mod_cast h2
  have e3 : z.2 ≤ 2 := by exact_mod_cast h3
  have e4 : z.2 - z.1 ≤ 1 := by exact_mod_cast h4
  have e5 : z.1 ≤ 2 * z.2 := by exact_mod_cast h5
  have hcase : z = ((0 : ℤ), (0 : ℤ)) ∨ z = ((0 : ℤ), (1 : ℤ)) ∨ z = ((1 : ℤ), (1 : ℤ)) ∨
      z = ((1 : ℤ), (2 : ℤ)) ∨ z = ((2 : ℤ), (1 : ℤ)) ∨ z = ((2 : ℤ), (2 : ℤ)) := by
    obtain ⟨a, b⟩ := z
    simp only [Prod.ext_iff] at *
    omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **`:518` 台架上 `(2,1,1)` 的残项，锚点无关形。**  桥的两条侧条件是
`(1,0) ∈ hexF`（`decide`）与 `latticeConvex_hexF_erase10`。 -/
theorem genClosure_518 :
    sh518 2 1 ⊆ {z | Colle37.GenClosure hexF (Ai 2 ∪ sh518 1 1) z} := by
  intro z hz
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (fillCover_518_gen10 hz)
  exact GenClosureWeaken.genFill_subset_genClosure (by decide) latticeConvex_hexF_erase10 n z hn

/-- ⭐ **`FillCoverStrip` 的三条量词在 `:518` 台架上同时兑现** ⟹ 加守卫之后的派单目标
**非空真**，值得投证明力。⚠ 第三格只在 `(2,1,1)` 上测到，见本节抬头那张表。 -/
theorem fillCoverStrip_positive_control :
    (∀ i ε : ℕ, sh518 i ε ⊆ {z | z + ((0 : ℕ) : ℤ) • ((0 : ℤ), (-1 : ℤ)) ∈
        Colle35.halfStrip (Ai i) ((0 : ℤ), (-1 : ℤ))}) ∧
    (∀ i ε : ℕ, ε + 1 ≤ i → EnvOf (↑hexF : Set (ℤ × ℤ))
        (ShellMink.shellInter (Ai i)
          (MaxEnv.shell (⋃ k, Ai k) ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ε)
          ((-1 : ℤ), (-1 : ℤ)))) ∧
    sh518 2 1 ⊆ {z | Colle37.GenClosure hexF (Ai 2 ∪ sh518 1 1) z} :=
  ⟨fun i ε => shellSubStrip_518 i ε, fun _ _ hi => envOf_shell518_transverse hi,
    genClosure_518⟩

/-- ⛔ **`not_fillCover_518_gen00` 否的是锚点，不是字段。**  同一台架、同一 `(2,1,1)`，
两半钉在一条语句里：`gen = (0,0)` 的单锚点滤链为假，而锚点无关的 `GenClosure` 形为真。 -/
theorem gen00_false_but_genClosure_true :
    ¬ (sh518 2 1 ⊆ ⋃ n, genFill hexF ((0 : ℤ), (0 : ℤ)) (Ai 2 ∪ sh518 1 1) n) ∧
    sh518 2 1 ⊆ {z | Colle37.GenClosure hexF (Ai 2 ∪ sh518 1 1) z} :=
  ⟨not_fillCover_518_gen00, genClosure_518⟩

/-! ## §10. 残项从「一个点」升级成「全称」——做功的是**包络守卫**，不是条带守卫

第 235 轮（lane-leafa-gen）。§9 只测到 `(i,i₀,ε) = (2,1,1)` 一格；本节把它做成全称，
并在过程中找到缺件的真身。

1. **本台架上 `EnvOf ↑hexF (sh518 i ε) ⟺ ε < i`**（`envOf_sh518_iff`）。正面早有
   （`envOf_shell518_transverse`，`ε + 1 ≤ i`）；反面是本节新的（`not_envOf_sh518_of_le`：
   `i ≤ ε` 时 `(0,-1)` 的暴露面塌成单点 `(0,-i)`，六条边掉成五条）。
2. ⟹ 字段里的包络守卫 `∀ i ≥ i₀, EnvOf …` 只要在 `i = i₀` 处求一次值，就**白送 `ε < i₀`**
   （`eps_lt_of_envGuard`）。这条信息字段表一直有，从来没人用过。
3. 有了 `ε ≤ i₀`，窗口式残项在本台架上**对一切 `i ≥ i₀` 成立**（`window_518`）。
4. ⛔ 而且是**尖锐**的：`i₀ < ε` 时残项为假（`not_window_518_of_lt`，见证 `(0,-(i₀+1))`
   在第 `i₀+1` 层）。⟹ `ε ≤ i₀` 不是证明的方便，是本台架上的充要条件。
5. ⭐ capstone `genClosure_518_universal` / `fillCover_518_field_shape`：`fillCover` 字段的
   结论在本台架上对**每一组**满足包络守卫的 `(ε, i₀, i)` 成立。

### ⭐ 鉴别性（PROTOCOL §52 / §84）：条带守卫在本台架上是**惰性**的

`fillCover_518_field_shape` 把 `:520` 右半的条带守卫写成第五个 binder，而签名里它是 `_`：
证明体一个字都没用它（`0 < ε` 同样没用上）。做功的是第三个 binder（包络守卫）在 `i = i₀`
处的那一次求值。⟹ 第 234 轮把希望押在「字段 ＋ `:520` 右半当假设」上，押错了那条假设。

### ⚠ 对 §9 收据的辖域订正（PROTOCOL §14，就地改，什么都不删）

`fillCoverStrip_positive_control` 的残项格取 `(i,i₀,ε) = (2,1,1)`。按第 1 条，
`EnvOf ↑hexF (sh518 1 1)` **为假**（`not_envOf_sh518_one_one`），所以在字段自己的 binder
形状里（包络守卫是 `∀ i ≥ i₀`，`i₀ = 1` 要在 `i = 1` 处成立）那一格落在**前件为假**的区域。
本节的全称版不吃这个问题：`eps_lt_of_envGuard` 先把 `ε < i₀` 逼出来。
§71 非空真见证：`ε = 1, i₀ = 2`（`envGuard_518_satisfiable`）。

### 射程（PROTOCOL §54）

⛔ 以上全部是 `Ai` / `hexF` / `gen = (1,0)` 这一组数据上的话。
⛔ **不**主张一般构型下「包络守卫 ⟹ `ε < i₀`」——那是本台架上 `E` 掉边的算术；一般构型下
   对应的问句是「`collarY i₀ ε` 是否厚过 `ε`」，本节一个字没说。
⛔ 不主张链上的 `fillCover` 字段为真。
-/

/-! ### §10.1 本台架上包络守卫 ⟺ `ε < i` -/

/-- `(0,-1)` 是 `↑hexF` 的一条边法向（`E_hexA_eq` 的六条之一）。 -/
theorem zeroNegOne_mem_E_hexF : ((0 : ℤ), (-1 : ℤ)) ∈ E (↑hexF : Set (ℤ × ℤ)) := by
  rw [coe_hexF, E_hexA_eq]
  simp only [hexE, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- `i ≤ ε` 时 `(0,-i)` 确实在 `sh518 i ε` 里（下界 `-ε` 松于斜边 `x - y ≤ i`）。 -/
theorem bot_pt_mem_sh518 {i ε : ℕ} (h : i ≤ ε) : ((0 : ℤ), -(i : ℤ)) ∈ sh518 i ε := by
  rw [sh518_eq]
  simp only [mem_hexShape]
  omega

/-- ⭐ **`i ≤ ε` 时 `(0,-1)` 的暴露面塌成单点。**  `dot (0,-1) z = -z.2 ≤ i - z.1 ≤ i`，
等号迫使 `z.1 = 0`；这就是「底边掉了」的内核形。 -/
theorem face_sh518_zeroNegOne {i ε : ℕ} (h : i ≤ ε) :
    face (sh518 i ε) ((0 : ℤ), (-1 : ℤ)) = {((0 : ℤ), -(i : ℤ))} := by
  have hle : ∀ z ∈ sh518 i ε, dot ((0 : ℤ), (-1 : ℤ)) z ≤ (i : ℤ) := by
    intro z hz
    rw [sh518_eq] at hz
    simp only [mem_hexShape] at hz
    simp only [dot]
    omega
  have hmem : ∃ z ∈ sh518 i ε, dot ((0 : ℤ), (-1 : ℤ)) z = (i : ℤ) :=
    ⟨_, bot_pt_mem_sh518 h, by simp [dot]⟩
  rw [face_eq_of_support hle hmem]
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hzT, hzd⟩
    rw [sh518_eq] at hzT
    simp only [mem_hexShape] at hzT
    simp only [dot] at hzd
    exact Prod.ext (by omega) (by omega)
  · rintro rfl
    exact ⟨bot_pt_mem_sh518 h, by simp [dot]⟩

theorem not_isEdge_sh518_zeroNegOne {i ε : ℕ} (h : i ≤ ε) :
    ((0 : ℤ), (-1 : ℤ)) ∉ E (sh518 i ε) := by
  rintro ⟨-, hnt⟩
  rw [face_sh518_zeroNegOne h] at hnt
  exact Set.not_nontrivial_singleton hnt

/-- ⭐ **`i ≤ ε` 时包络守卫为假。**  `envOf_shell518_transverse` 的**反面**，本件新的。 -/
theorem not_envOf_sh518_of_le {i ε : ℕ} (h : i ≤ ε) :
    ¬ EnvOf (↑hexF : Set (ℤ × ℤ)) (sh518 i ε) := by
  intro hE
  have hss : E (sh518 i ε) ⊂ E (↑hexF : Set (ℤ × ℤ)) :=
    ⟨hE.1.E_subset, fun hsup => not_isEdge_sh518_zeroNegOne h (hsup zeroNegOne_mem_E_hexF)⟩
  exact absurd hE.2 (ne_of_lt ((finite_E_hexF.subset hE.1.E_subset).encard_lt_encard hss))

/-- 把 `sh518`（外层写 `quad`）与 `envOf_shell518_transverse`（外层写 `⋃ k, Ai k`）钉成同一集合。 -/
theorem sh518_eq_collar (i ε : ℕ) :
    sh518 i ε = ShellMink.shellInter (Ai i)
      (MaxEnv.shell (⋃ k, Ai k) ((0 : ℤ), (-1 : ℤ)) ((0 : ℤ), (1 : ℤ)) 0 ε)
      ((-1 : ℤ), (-1 : ℤ)) := by
  rw [iUnion_Ai_eq_quad]
  rfl

theorem envOf_sh518 {i ε : ℕ} (hi : ε < i) : EnvOf (↑hexF : Set (ℤ × ℤ)) (sh518 i ε) := by
  rw [sh518_eq_collar]
  exact envOf_shell518_transverse hi

/-- ⭐ **本台架上包络守卫的充要条件。** -/
theorem envOf_sh518_iff (i ε : ℕ) :
    EnvOf (↑hexF : Set (ℤ × ℤ)) (sh518 i ε) ↔ ε < i := by
  refine ⟨fun h => ?_, envOf_sh518⟩
  by_contra hc
  exact not_envOf_sh518_of_le (Nat.le_of_not_lt hc) h

/-- ⭐⭐ **包络守卫在 `i = i₀` 处白送 `ε < i₀`。**  这是本件找到的「缺件」：
字段表已经有这条信息，只是从来没人在 `i = i₀` 处求值过。 -/
theorem eps_lt_of_envGuard {ε i₀ : ℕ}
    (henv : ∀ i, i₀ ≤ i → EnvOf (↑hexF : Set (ℤ × ℤ)) (sh518 i ε)) : ε < i₀ :=
  (envOf_sh518_iff i₀ ε).mp (henv i₀ le_rfl)

/-- §71 非空真见证：`ε = 1, i₀ = 2` 时包络守卫可满足。 -/
theorem envGuard_518_satisfiable :
    ∀ i, 2 ≤ i → EnvOf (↑hexF : Set (ℤ × ℤ)) (sh518 i 1) :=
  fun _ hi => envOf_sh518 hi

/-- ⚠ 上一轮那一格 `(i,i₀,ε) = (2,1,1)` 的包络守卫在 `i = i₀ = 1` 处**为假**。 -/
theorem not_envOf_sh518_one_one : ¬ EnvOf (↑hexF : Set (ℤ × ℤ)) (sh518 1 1) :=
  not_envOf_sh518_of_le le_rfl

/-! ### §10.2 残项（窗口式）在 `ε ≤ i₀` 下全称成立 -/

/-- ⭐ **本台架上的残项，全称版。**  `y ≥ 0` 落进 `Ai i`；`y < 0 ∧ x = 0` 落进 `sh518 i₀ ε`
（这一步用 `ε ≤ i₀`）；其余 `x ≥ 1`，七个窗口偏移全部留在 `sh518 i ε` 里
（`x = 2i` 与 `y ≤ -1` 不相容，所以右端也不越界）。 -/
theorem window_518 {ε i₀ i : ℕ} (hle : ε ≤ i₀) (hi : i₀ ≤ i) (hi₀ : 0 < i₀)
    {z : ℤ × ℤ} (hz : z ∈ sh518 i ε) :
    z ∈ Ai i ∪ sh518 i₀ ε ∨
      ∀ b ∈ hexF, z + (b - ((1 : ℤ), (0 : ℤ))) ∈ sh518 i ε := by
  obtain ⟨x, y⟩ := z
  rw [sh518_eq] at hz
  simp only [mem_hexShape] at hz
  by_cases hy : 0 ≤ y
  · refine Or.inl (Or.inl ?_)
    simp only [Ai, mem_hexShape]
    omega
  · by_cases hx : x = 0
    · refine Or.inl (Or.inr ?_)
      rw [sh518_eq]
      simp only [mem_hexShape]
      omega
    · refine Or.inr ?_
      intro b hb
      simp only [hexF, Finset.mem_insert, Finset.mem_singleton] at hb
      rw [sh518_eq]
      simp only [mem_hexShape, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- ⛔ **尖锐：`i₀ < ε` 时残项为假**，见证 `(0, -(i₀+1))` 在 `i = i₀ + 1` 层。
它既不在 `Ai (i₀+1)` 里（`y < 0`），也不在 `sh518 i₀ ε` 里（`x - y = i₀+1 > i₀`），
而窗口偏移 `b = (0,0)` 把它推到 `x = -1`。⟹ `ε ≤ i₀` 是台架上的**充要**条件。 -/
theorem not_window_518_of_lt {ε i₀ : ℕ} (h : i₀ < ε) :
    ¬ (∀ z ∈ sh518 (i₀ + 1) ε, z ∈ Ai (i₀ + 1) ∪ sh518 i₀ ε ∨
        ∀ b ∈ hexF, z + (b - ((1 : ℤ), (0 : ℤ))) ∈ sh518 (i₀ + 1) ε) := by
  intro hw
  have hmem : ((0 : ℤ), -((i₀ : ℤ) + 1)) ∈ sh518 (i₀ + 1) ε := by
    rw [sh518_eq]
    simp only [mem_hexShape]
    omega
  rcases hw _ hmem with (hA | hY) | hb
  · simp only [Ai, mem_hexShape] at hA
    omega
  · rw [sh518_eq] at hY
    simp only [mem_hexShape] at hY
    omega
  · have hz0 := hb ((0 : ℤ), (0 : ℤ)) (by simp [hexF])
    rw [sh518_eq] at hz0
    simp only [mem_hexShape, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hz0
    omega

/-! ### §10.3 capstone：`fillCover` 的结论在本台架上全称成立 -/

/-- 秩协向量：`n' = (-1,3)` 在 `hexF` 上把 `(1,0)` 钉成严格极小
（值分别为 `-1 < 0,1,2,3,4,5`）。⚠ 这里**不**走 `exists_lex_covector`，
因为本台架没有 `FaceBlock` 见证；协向量是直接给出的。 -/
theorem covector_hexF_gen10 :
    ∀ b ∈ hexF.erase ((1 : ℤ), (0 : ℤ)),
      dot ((-1 : ℤ), (3 : ℤ)) ((1 : ℤ), (0 : ℤ)) < dot ((-1 : ℤ), (3 : ℤ)) b := by
  intro b hb
  obtain ⟨hne, hb'⟩ := Finset.mem_erase.1 hb
  simp only [hexF, Finset.mem_insert, Finset.mem_singleton] at hb'
  rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num [dot]
  · exact absurd rfl hne
  · norm_num [dot]
  · norm_num [dot]
  · norm_num [dot]
  · norm_num [dot]
  · norm_num [dot]

/-- 协向量归纳：秩取 `(6i + 1 - ⟪n', z⟫).toNat`，每一步 `⟪n', ·⟫` 严格上升。
⚠ 走的是 `MaxEnv.subset_genClosure_of_rank`（已在闭包里），**不**引入
`FillCoverReduce` 的 `subset_genClosure_of_covector` —— 只为不给
`FillCoverWitness.lean` 新加 import 边（工具盲区 2）。 -/
theorem genFill_518_universal {ε i₀ i : ℕ} (hle : ε ≤ i₀) (hi : i₀ ≤ i) (hi₀ : 0 < i₀) :
    sh518 i ε ⊆ MaxEnv.genClosure hexF ((1 : ℤ), (0 : ℤ)) (Ai i ∪ sh518 i₀ ε) := by
  have hbdd : ∀ z ∈ sh518 i ε, dot ((-1 : ℤ), (3 : ℤ)) z ≤ 6 * (i : ℤ) := by
    intro z hz
    rw [sh518_eq] at hz
    simp only [mem_hexShape] at hz
    simp only [dot]
    omega
  refine MaxEnv.subset_genClosure_of_rank
    (fun z => (6 * (i : ℤ) + 1 - dot ((-1 : ℤ), (3 : ℤ)) z).toNat) ?_
  intro z hz
  rcases window_518 hle hi hi₀ hz with hx | hw
  · exact Or.inl hx
  · refine Or.inr ⟨z - ((1 : ℤ), (0 : ℤ)), by abel, fun b hb => ?_⟩
    have hrw : b + (z - ((1 : ℤ), (0 : ℤ))) = z + (b - ((1 : ℤ), (0 : ℤ))) := by abel
    rw [hrw]
    refine Or.inr ⟨hw b (Finset.mem_of_mem_erase hb), ?_⟩
    have h1 := covector_hexF_gen10 b hb
    have h2 : dot ((-1 : ℤ), (3 : ℤ)) (z + (b - ((1 : ℤ), (0 : ℤ)))) =
        dot ((-1 : ℤ), (3 : ℤ)) z +
          (dot ((-1 : ℤ), (3 : ℤ)) b - dot ((-1 : ℤ), (3 : ℤ)) ((1 : ℤ), (0 : ℤ))) := by
      simp only [dot, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
      ring
    have h3 := hbdd z hz
    omega

/-- ⭐⭐ **`:518` 台架上 `fillCover` 的结论，全称版。**  前件只有包络守卫；
`ε < i₀` 由 `eps_lt_of_envGuard` 从它里面取出，残项由 `window_518` 兑现，
协向量归纳由 `genFill_518_universal` 走完，锚点无关化由
`genClosure_subset_genClosure` ＋ `latticeConvex_hexF_erase10`。 -/
theorem genClosure_518_universal {ε i₀ : ℕ}
    (henv : ∀ i, i₀ ≤ i → EnvOf (↑hexF : Set (ℤ × ℤ)) (sh518 i ε)) :
    ∀ i, i₀ ≤ i → sh518 i ε ⊆ {z | Colle37.GenClosure hexF (Ai i ∪ sh518 i₀ ε) z} := by
  have hlt : ε < i₀ := eps_lt_of_envGuard henv
  have hi₀ : 0 < i₀ := by omega
  intro i hi z hz
  exact GenClosureWeaken.genClosure_subset_genClosure (by decide)
    latticeConvex_hexF_erase10 z (genFill_518_universal hlt.le hi hi₀ hz)

/-- ⭐ **写成字段自己的 binder 形状**（`0 < ε` / `0 < i₀` / 包络守卫 / `:520` 右半条带守卫 /
`max i₀ I₀ ≤ i`），对**一切** `I₀`。

⛔⭐ **第四、第五个 binder 在签名里是 `_`：条带守卫与 `0 < ε` 一个字都没用上。**
本台架上做功的是包络守卫在 `i = i₀` 处的那一次求值。这是本件的鉴别性结论：
`FillCoverStrip` 押在 `:520` 右半上的那部分希望，在本台架上是**惰性**的。 -/
theorem fillCover_518_field_shape (I₀ : ℕ) :
    ∀ ε i₀ : ℕ, 0 < ε → 0 < i₀ →
      (∀ i, i₀ ≤ i → EnvOf (↑hexF : Set (ℤ × ℤ)) (sh518 i ε)) →
      (∀ i, max i₀ I₀ ≤ i → sh518 i ε ⊆ {z | z + ((0 : ℕ) : ℤ) • ((0 : ℤ), (-1 : ℤ)) ∈
        Colle35.halfStrip (Ai i) ((0 : ℤ), (-1 : ℤ))}) →
      ∀ i, max i₀ I₀ ≤ i →
        sh518 i ε ⊆ {z | Colle37.GenClosure hexF (Ai i ∪ sh518 i₀ ε) z} :=
  fun _ _ _ _ henv _ i hi => genClosure_518_universal henv i (le_trans (le_max_left _ _) hi)

end Nivat.FillCoverWit

#print axioms Nivat.FillCoverWit.convex_pent
#print axioms Nivat.FillCoverWit.latticeConvex_hexF_erase10
#print axioms Nivat.FillCoverWit.genClosure_518
#print axioms Nivat.FillCoverWit.fillCoverStrip_positive_control
#print axioms Nivat.FillCoverWit.gen00_false_but_genClosure_true

#print axioms Nivat.FillCoverWit.zeroNegOne_mem_E_hexF
#print axioms Nivat.FillCoverWit.bot_pt_mem_sh518
#print axioms Nivat.FillCoverWit.face_sh518_zeroNegOne
#print axioms Nivat.FillCoverWit.not_isEdge_sh518_zeroNegOne
#print axioms Nivat.FillCoverWit.not_envOf_sh518_of_le
#print axioms Nivat.FillCoverWit.sh518_eq_collar
#print axioms Nivat.FillCoverWit.envOf_sh518
#print axioms Nivat.FillCoverWit.envOf_sh518_iff
#print axioms Nivat.FillCoverWit.eps_lt_of_envGuard
#print axioms Nivat.FillCoverWit.envGuard_518_satisfiable
#print axioms Nivat.FillCoverWit.not_envOf_sh518_one_one
#print axioms Nivat.FillCoverWit.window_518
#print axioms Nivat.FillCoverWit.not_window_518_of_lt
#print axioms Nivat.FillCoverWit.covector_hexF_gen10
#print axioms Nivat.FillCoverWit.genFill_518_universal
#print axioms Nivat.FillCoverWit.genClosure_518_universal
#print axioms Nivat.FillCoverWit.fillCover_518_field_shape

#print axioms Nivat.FillCoverWit.exists_of_pos_i₀
#print axioms Nivat.FillCoverWit.shellEnv_field_at_vJ1_square_pos
#print axioms Nivat.FillCoverWit.not_shellEnv_field_at_vJ1_pos

#print axioms Nivat.FillCoverWit.not_fillCover_singleSweep
#print axioms Nivat.FillCoverWit.not_fillCover_singleSweep_gen00
#print axioms Nivat.FillCoverWit.not_fillCover_singleSweep_gen10
#print axioms Nivat.FillCoverWit.fillCover_518_gen10
#print axioms Nivat.FillCoverWit.not_fillCover_518_gen00
#print axioms Nivat.FillCoverWit.shellSubStrip_518
#print axioms Nivat.FillCoverWit.coe_hexF
#print axioms Nivat.FillCoverWit.fillCover_binder_false
#print axioms Nivat.FillCoverWit.fillCover_binder_false_gen00
#print axioms Nivat.FillCoverWit.not_envOf_shell_Ai
#print axioms Nivat.FillCoverWit.fillCover_field_vacuous_at_vJ1
#print axioms Nivat.FillCoverWit.not_shellEnv_field_at_vJ1
#print axioms Nivat.FillCoverWit.iUnion_Ai_eq_quad
#print axioms Nivat.FillCoverWit.envOf_shell518_transverse
#print axioms Nivat.FillCoverWit.det_vl_w_discriminates
#print axioms Nivat.FillCoverWit.hatOf_zero_gen
#print axioms Nivat.FillCoverWit.coe_sqF
#print axioms Nivat.FillCoverWit.iUnion_sqBx_eq_quad
#print axioms Nivat.FillCoverWit.swept_sqBx
#print axioms Nivat.FillCoverWit.shell_sqBx_eq
#print axioms Nivat.FillCoverWit.shellInter_sqBx_vJ1_eq
#print axioms Nivat.FillCoverWit.shellEnv_field_at_vJ1_square
#print axioms Nivat.FillCoverWit.not_shellEnv_imp_det_ne_zero
#print axioms Nivat.FillCoverWit.not_shellEnv_imp_det_ne_zero_pos
#print axioms Nivat.FillCoverWit.not_shellEnv_imp_det_ne_zero_of_pos
#print axioms Nivat.FillCoverWit.E_shell_eq_of_shellEnv_at_vJ1
#print axioms Nivat.FillCoverWit.hexF_rising_normal
#print axioms Nivat.FillCoverWit.sqF_no_rising_normal
#print axioms Nivat.FillCoverWit.faceBlock_a_sqF
#print axioms Nivat.FillCoverWit.faceBlock_a'_sqF
