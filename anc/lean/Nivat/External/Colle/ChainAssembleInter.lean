/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainAssemble
import Nivat.External.Colle.ShellMink

/-!
# `ChainDataGeom.ofParts`, with `shell` swapped from `MaxEnv.shell` to `ShellMink.shellInter`

Lane `lane-shell`, 2026-09-22.  `ChainAssemble.lean:233-235` instantiates the `shell` field of
`ChainDataGeom.ofParts` as the single sweep `MaxEnv.shell (hatOf A kk vl i) vJ1 nJ cJ ε`
(`b3_colle2.txt:440`).  Lane-leafa's kernel receipts
(`tmp/wip/shell_aenvfix_fillCover_wit.lean`, ported from `blueprint/ARCHIVE`) show this
instantiation is **dead**: `fillCover` is false at every generator with `gen.1 ≤ 1` (in
particular both candidate face endpoints) on that construction (`not_fillCover_singleSweep`),
and `shellSubStrip` is unconditionally false whenever the sweep direction is transverse to `vl`
(`ShellMink.not_shellSubStrip_of_transverse_sweep`).  Neither is "unproved"; both are refuted.

The paper's literal formula at `:518` is different: `Â_i^{(ε)} := {g − t·v_{ℓ_{J+1}} ∈
Â_∞^{(ε)} : g ∈ Â_i, t ∈ ℤ₊}`, i.e. the sweep of `Â_i` along `w := −v_{ℓ_{J+1}}` **intersected**
with the already-built outer shell `Â_∞^{(ε)}` — `ShellMink.shellInter A Ainf w :=
reachSet A w ∩ Ainf` (`ShellMink.lean:507`).  On the same numeric instance the `:518` object is
**not** refuted: `fillCover` holds there for `gen = (1,0) = F.a'` (the `vJ`-forward face
endpoint, matching the `gen_eq : gen = F.a'` ruling already in `ofParts`) and `shellSubStrip`
is reproved directly against the new object (`shellSubStrip_518`, `J = ι+1` configuration,
`w` transverse to `vJ1`, `vl` parallel to `vJ1`).

`w := −v_{ℓ_{J+1}}` is genuinely new data: nothing in `ChainDataGeom`/`ChainDataWithShell`
names `v_{ℓ_{J+1}}`, so `ofPartsInter` below takes it as an extra parameter rather than
reusing `vJ1`.  See `blueprint/LEAF-A.md`, "2026-09-22（lane-shell）: shell 换成 shellInter"
for the field-by-field accounting this file implements.

## What is free once `shell i ε := shellInter (Ahat i) (shellInf ε) w`

* `shellSubInf` (`shell i ε ⊆ shellInf ε`) is **unconditionally free** —
  `ShellMink.shellInter_subset_right` — no hypothesis at all, stronger than the
  `MaxEnv.shell` case (`shell_mono_set`, which still needed the chain's monotonicity).
* `subShell` (`Ahat i ⊆ shell i ε`) is free given the same `hhp` `ofParts` already takes:
  `Ahat i ⊆ ⋃ j, Ahat j ⊆ shellInf ε` (`MaxEnv.subset_shell`), then
  `ShellMink.subset_shellInter`.
* `shellFinite` needs one new hypothesis, `hsweepW : dot nJ w < 0` (the `w`-analogue of the
  existing `hsweep : dot nJ vJ1 < 0`): any `z ∈ shellInter (Ahat i) (shellInf ε) w` is both a
  `w`-translate of a point of `Ahat i` *and* satisfies `cJ - ε ≤ dot nJ z` (inherited from
  membership in `shellInf ε = MaxEnv.shell (⋃ Ahat) vJ1 nJ cJ ε`, whose defining inequality is
  read off the point itself, not the witness `g' t' v`) — so
  `shellInter (Ahat i) (shellInf ε) w ⊆ MaxEnv.shell (Ahat i) w nJ cJ ε`
  (`shellInter_subset_shell` below), and the right side is finite by `MaxEnv.shell_finite`
  given `hfin i` and `hsweepW`.
* `shellInfZero`, `fillZero`, `fillStep` are untouched: `shellInfZero` only talks about
  `shellInf`, which keeps the old `MaxEnv.shell (⋃ Ahat) vJ1 nJ cJ` formula (`shellInf_eq` is
  still `rfl`); `fillZero`/`fillStep` are about `genFill` applied to an opaque starting set and
  never unfold `shell`'s formula.
* `shellProper` is discharged from a **`w`-escape witness** (`escapeW` below, the `w`-analogue
  of `ofParts`'s `escape`) via `ShellMink.not_shellInter_subset`, which additionally demands
  the escaping point land *inside* `shellInf ε` — a strictly stronger request than the old
  `escape`, matching the fact that `shellInter` can be strictly smaller than the plain sweep
  (`ShellMink.shellInter_transverse_collapses` is the cautionary example that this can fail).

## What stays a hypothesis, unresolved

`shellSubStrip`, `shellEnv`, `fillCover` are kept as hypotheses of `ofPartsInter`, restated
against `shellInter (Ahat i) (shellInf ε) w` in place of `MaxEnv.shell (Ahat i) vJ1 nJ cJ ε`.
Unlike on the old object, none of these three is refuted on `shellInter`; the `(i,i₀,ε) =
(2,1,1)` instance in `tmp/wip/shell_aenvfix_fillCover_wit.lean` is positive evidence for all
three being satisfiable when `gen = F.a'`, `w` transverse to `vJ1`.  Proving them for a general
`ChainDataGeom` (rather than one numeric instance) is real, shape-specific geometry that this
file does not attempt (PROTOCOL §20: a binder that does not close mechanically stays a
hypothesis).  `escapeW`/`shellEnv`/`fillCover`/`shellSubStrip` at `J > ι+1` (`w` transverse to
`vl`, not just to `vJ1`) are flagged in `blueprint/LEAF-A.md` as untested even on the numeric
instance.
-/

set_option autoImplicit false

namespace Nivat.ChainAsm

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.ShellMink

variable {α : Type*}

/-! ## §1. The free shell-block lemmas for `shellInter`, ported from the `ofParts` pattern -/

section InterBlock

variable {Ac : ℕ → Set (ℤ × ℤ)} {v n : ℤ × ℤ} {c : ℤ}

/-- Any point of `shellInter (Ac i) (MaxEnv.shell (⋃ Ac) v n c ε) w` is a `w`-translate of a
point of `Ac i`, at level `≥ c - ε` — i.e. it already sits in the plain `w`-sweep shell of
`Ac i` (no dependence on `v`).  The reachability component of `shellInf`'s witness is simply
dropped. -/
theorem shellInter_subset_shell (A A' : Set (ℤ × ℤ)) (w : ℤ × ℤ) (ε : ℕ) :
    ShellMink.shellInter A (MaxEnv.shell A' v n c ε) w ⊆ MaxEnv.shell A w n c ε := by
  rintro z ⟨⟨g, hg, t, rfl⟩, g', hg', t', -, hlev⟩
  exact ⟨g, hg, t, rfl, hlev⟩

/-- **`ChainData.shellFinite` for the intersection form.**  Needs `dot n w < 0` (the
`w`-analogue of the old `hsweep`), not `dot n v < 0`. -/
theorem shellInterFinite_of (hfin : ∀ i, (Ac i).Finite) {w : ℤ × ℤ} (hw : dot n w < 0)
    (i ε : ℕ) :
    (ShellMink.shellInter (Ac i) (MaxEnv.shell (⋃ j, Ac j) v n c ε) w).Finite :=
  (MaxEnv.shell_finite (hfin i) hw).subset (shellInter_subset_shell (Ac i) (⋃ j, Ac j) w ε)

/-- **`ChainData.subShell` for the intersection form.**  Same `hhp` as `ofParts` already
takes. -/
theorem subShellInter_of (hhp : ∀ i, Ac i ⊆ halfPlaneGE n c) (w : ℤ × ℤ) (i ε : ℕ) :
    Ac i ⊆ ShellMink.shellInter (Ac i) (MaxEnv.shell (⋃ j, Ac j) v n c ε) w :=
  ShellMink.subset_shellInter
    ((Set.subset_iUnion Ac i).trans (MaxEnv.subset_shell ε (Set.iUnion_subset hhp))) w

/-- **`ChainData.shellSubInf` for the intersection form: unconditionally free.** -/
theorem shellSubInfInter_of (w : ℤ × ℤ) (i ε : ℕ) :
    ShellMink.shellInter (Ac i) (MaxEnv.shell (⋃ j, Ac j) v n c ε) w ⊆
      MaxEnv.shell (⋃ j, Ac j) v n c ε :=
  ShellMink.shellInter_subset_right _ _ w

/-- **`ChainData.shellProper` for the intersection form**, from a `w`-escape witness that
lands inside `shellInf ε` (strictly stronger than the old `escape`, since `shellInter` can be
smaller than the plain sweep). -/
theorem shellProperInter_of {i ε : ℕ} {g w : ℤ × ℤ} {t : ℕ} (hg : g ∈ Ac i)
    (hin : g + (t : ℤ) • w ∈ MaxEnv.shell (⋃ j, Ac j) v n c ε) (hout : g + (t : ℤ) • w ∉ Ac i) :
    ¬ ShellMink.shellInter (Ac i) (MaxEnv.shell (⋃ j, Ac j) v n c ε) w ⊆ Ac i :=
  ShellMink.not_shellInter_subset hg hin hout

end InterBlock

/-! ## §1.5. `b3_colle2.txt:520` 的**左**半：不是义务，是 `subBA` ＋ `hhp` 的推论

lane-leafa-gen, 2026-09-26（第 238 轮）。`:520` 逐字是**一句双侧夹逼**：

    B_i - k_i v⃗_ℓ ⊂ Â_i^{(ε)} ⊂ H_{B_i}(ℓ) - k_i v⃗_ℓ

**右**半已在结构里，是 `ChainDataGeomParts.shellSubStrip`（`ChainPartsFeed.lean:329`），
那是真的未证义务。**左**半一度被批准入字段（`shellSupB`），本轮查出可导出后撤销
（硬规矩 22：能从现有字段导出的义务不入字段，作为字段只是每个生产者都要兑现的死重）。
机制两步，都不需要新数据：

1. `Colle35.hatOf A kk vl i` 按**定义**就是平移后的 `A i`
   （`ChainMax.lean:87-88`，docstring 指 `b3_colle2.txt:488` 的 `Â_i := A_i − k_i v_ℓ`）。
   于是 `B_i - k_i v⃗_ℓ`（即 `{z | z + (kk i : ℤ) • vl ∈ B i}`）`⊆ Â_i` **就是**
   `subBA i : B i ⊆ A i`（`ChainPartsFeed.lean:230`）在同一平移下的像——同一个 `z`、
   同一个平移，不需要引理。
2. `Â_i ⊆ Â_i^{(ε)}` 是上面的 `subShellInter_of`，只吃已有的 `hhp`。
-/

section SupB

open Nivat.Colle35

variable {A B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl w v n : ℤ × ℤ} {c : ℤ}

/-- ⭐ **`b3_colle2.txt:520` 的左半，无守卫、对一切 `i ε` 成立。**
`B_i - k_i v⃗_ℓ ⊆ Â_i^{(ε)}`。 -/
theorem shellSupB_free
    (subBA : ∀ i, B i ⊆ A i)
    (hhp : ∀ i, hatOf A kk vl i ⊆ halfPlaneGE n c)
    (i ε : ℕ) :
    {z | z + (kk i : ℤ) • vl ∈ B i} ⊆
      ShellMink.shellInter (hatOf A kk vl i)
        (MaxEnv.shell (⋃ j, hatOf A kk vl j) v n c ε) w :=
  fun _z hz => subShellInter_of hhp w i ε (subBA i hz)

/-- **同一条的字段形包装**，binder 与 `shellSubStrip`（`ChainPartsFeed.lean:329`）逐字符同构。
⚠ **`hε` / `hEnv` / 尾守卫三个位置在证明项里全是 `_`**：这是「那三个守卫在本条上惰性」的
内核见证（§41 的读法），也是不把左半入字段的理由——入了会让下游误以为守卫在做功。 -/
theorem shellSupB_field_free {Env : Set (ℤ × ℤ) → Prop} {I₀ : ℕ}
    (subBA : ∀ i, B i ⊆ A i)
    (hhp : ∀ i, hatOf A kk vl i ⊆ halfPlaneGE n c) :
    ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → Env (ShellMink.shellInter (hatOf A kk vl i)
        (MaxEnv.shell (⋃ j, hatOf A kk vl j) v n c ε) w)) →
      ∀ i, max i₀ I₀ ≤ i →
      {z | z + (kk i : ℤ) • vl ∈ B i} ⊆
        ShellMink.shellInter (hatOf A kk vl i)
          (MaxEnv.shell (⋃ j, hatOf A kk vl j) v n c ε) w :=
  fun ε _i₀ _hε _hEnv i _hi => shellSupB_free subBA hhp i ε

/-- **`:520` 那一句的完整对应物**：左半免费，右半仍是假设。用途是让夹逼两半在 Lean 里并置,
而不必为左半付字段的代价。 -/
theorem shellSandwich_520
    (subBA : ∀ i, B i ⊆ A i)
    (hhp : ∀ i, hatOf A kk vl i ⊆ halfPlaneGE n c) {i ε : ℕ}
    (right : ShellMink.shellInter (hatOf A kk vl i)
        (MaxEnv.shell (⋃ j, hatOf A kk vl j) v n c ε) w ⊆
      {z | z + (kk i : ℤ) • vl ∈ Colle35.halfStrip (B i) vl}) :
    {z | z + (kk i : ℤ) • vl ∈ B i} ⊆
        ShellMink.shellInter (hatOf A kk vl i)
          (MaxEnv.shell (⋃ j, hatOf A kk vl j) v n c ε) w ∧
      ShellMink.shellInter (hatOf A kk vl i)
          (MaxEnv.shell (⋃ j, hatOf A kk vl j) v n c ε) w ⊆
        {z | z + (kk i : ℤ) • vl ∈ Colle35.halfStrip (B i) vl} :=
  ⟨shellSupB_free subBA hhp i ε, right⟩

end SupB

/-! ## §1.6. `0 < i₀`：三条义务侧的换值 wrapper

lane-leafa-gen, 2026-09-26（集成者裁决）。`b3_colle2.txt:520` 引进 `i₀` 的原句是
「**So let** `ε ∈ ℕ` **and** `i₀ ∈ ℕ` **be such that** `Â_{i₀}^{(ε)}` is an
`E(S_φ)`-enveloped set」——选**一对**值，没有「正」「最小」之类的要求。若下游需要
`0 < i₀`，**不为此加字段**（硬规矩 5：比原文强＝债），改为就地把 `i₀` 换成 `max i₀ 1`：
守卫侧经 `le_max_left` 反单调地保住，`0 < max i₀ 1` 由 `le_max_right` 给出。

⚠ **三条不是同一个代价，分界是「`i₀` 在结论体里出没出现」**：

| 义务 | `i₀` 的位置 | 换值代价 |
|---|---|---|
| `escapeW`（`ChainPartsFeed.lean:322`） | 守卫 ＋ 尾守卫 `max i₀ I₀` | 零 |
| `shellSubStrip`（同文件 `:329`） | 守卫 ＋ 尾守卫 | 零 |
| `fillCover`（同文件 `:343`） | 守卫 ＋ 尾守卫 ＋ **结论体的残量种子** `hatOf A kk vl i₀`（`:350`,本文件 `:220` 的同一项） | 结论被**减弱** |

第三个位置换值后种子变成 `Ac (max i₀ 1)`，经 `AhatMono` 种子变大 ⟹ `GenClosure` 的上界
集合变大 ⟹ 结论变弱。所以「`0 < i₀` 免费」要拆两句：**作为要证的义务，免费；作为可搬运的
结论，不免费**。形状级鉴别收据 `Nivat.LaneLeafAGenPosI0.seeded_shift_is_real`
（`tmp/wip/lane-leafa-gen-posi0.lean`）给出内核见证 `C ε i₀ i ∧ ¬ C ε (max i₀ 1) i` 可满足。

⚠ **但那个减弱在真实消费者处是惰性的**（读证明体所得，非转述）。全树搜
`\w+\.fillCover\b` 后，唯一带参数**应用**它的点是 `Lemma35.lean:1014`
（`c.fillCover ε i₀ hεpos hEnv (σ j) hmaxi hz`）。那里 `(ε, i₀)` 是 `:997` 从 `c.shellEnv`
**析构**出来的、不是消费者挑的；种子侧的 (3.3)（`:1004` 的 `h33`）是消费者自己用
`c.shellFinite i₀ ε`（`:1000` 取累积点）＋ `c.shellSubInf i₀ ε`（`:1008`）在**同一个** `i₀`
上搭的；其余用到 `i₀` 的地方（`:1001` / `:1002` / `:1018` / `:1027`）只要求 `i₀ ≤ σ j` 或
`max i₀ I₀ ≤ σ j`。⟹ 整块**一致地**抬到 `j₀`（累积点改取 `max j₀ I₀`）零损失。
⛔ 按 PROTOCOL §51 这只覆盖我读过的那**一个**消费点，不是「任何消费者都不在乎」；
对**非一致**的抬升（抬守卫、留种子）仍无解。
-/

section PosI₀

open Nivat.Colle35

variable {Ac : ℕ → Set (ℤ × ℤ)} {v n w : ℤ × ℤ} {c : ℤ} {I₀ : ℕ}
  {Env : Set (ℤ × ℤ) → Prop}

/-- `max i₀ 1` 是正的。 -/
theorem shellObl_pos_max_one (i₀ : ℕ) : 0 < max i₀ 1 :=
  lt_of_lt_of_le one_pos (le_max_right i₀ 1)

/-- 守卫对下界反单调：把 `i₀` 抬到任何 `j₀ ≥ i₀` 都还成立。 -/
theorem shellObl_guard_of_le {Q : ℕ → Prop} {i₀ j₀ : ℕ} (hij : i₀ ≤ j₀)
    (hg : ∀ i, i₀ ≤ i → Q i) : ∀ i, j₀ ≤ i → Q i :=
  fun i hi => hg i (le_trans hij hi)

/-- **`escapeW` 侧的 `0 < i₀`**（`ChainPartsFeed.lean:322` 的 binder 形，
`Ac := hatOf A kk vl`）：纯守卫换值，结论体不含 `i₀`。 -/
theorem shellObl_escapeW_pos_i₀
    (h : ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → Env (ShellMink.shellInter (Ac i)
        (MaxEnv.shell (⋃ j, Ac j) v n c ε) w)) →
      ∀ i, max i₀ I₀ ≤ i → ∃ g ∈ Ac i, ∃ t : ℕ,
        g + (t : ℤ) • w ∈ MaxEnv.shell (⋃ j, Ac j) v n c ε ∧ g + (t : ℤ) • w ∉ Ac i)
    (ε i₀ : ℕ) (hε : 0 < ε)
    (hg : ∀ i, i₀ ≤ i → Env (ShellMink.shellInter (Ac i)
      (MaxEnv.shell (⋃ j, Ac j) v n c ε) w)) :
    ∃ j₀ : ℕ, 0 < j₀ ∧ i₀ ≤ j₀ ∧
      (∀ i, j₀ ≤ i → Env (ShellMink.shellInter (Ac i)
        (MaxEnv.shell (⋃ j, Ac j) v n c ε) w)) ∧
      (∀ i, max j₀ I₀ ≤ i → ∃ g ∈ Ac i, ∃ t : ℕ,
        g + (t : ℤ) • w ∈ MaxEnv.shell (⋃ j, Ac j) v n c ε ∧ g + (t : ℤ) • w ∉ Ac i) :=
  ⟨max i₀ 1, shellObl_pos_max_one i₀, le_max_left i₀ 1,
    shellObl_guard_of_le (le_max_left i₀ 1) hg,
    h ε (max i₀ 1) hε (shellObl_guard_of_le (le_max_left i₀ 1) hg)⟩

/-- **`shellSubStrip` 侧的 `0 < i₀`**（`ChainPartsFeed.lean:329` 的 binder 形）：
纯守卫换值。`b3_colle2.txt:520` 的右半，结论体不含 `i₀`。 -/
theorem shellObl_shellSubStrip_pos_i₀ {B : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ} {vl : ℤ × ℤ}
    (h : ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → Env (ShellMink.shellInter (Ac i)
        (MaxEnv.shell (⋃ j, Ac j) v n c ε) w)) →
      ∀ i, max i₀ I₀ ≤ i →
      ShellMink.shellInter (Ac i) (MaxEnv.shell (⋃ j, Ac j) v n c ε) w ⊆
        {z | z + (kk i : ℤ) • vl ∈ Colle35.halfStrip (B i) vl})
    (ε i₀ : ℕ) (hε : 0 < ε)
    (hg : ∀ i, i₀ ≤ i → Env (ShellMink.shellInter (Ac i)
      (MaxEnv.shell (⋃ j, Ac j) v n c ε) w)) :
    ∃ j₀ : ℕ, 0 < j₀ ∧ i₀ ≤ j₀ ∧
      (∀ i, j₀ ≤ i → Env (ShellMink.shellInter (Ac i)
        (MaxEnv.shell (⋃ j, Ac j) v n c ε) w)) ∧
      (∀ i, max j₀ I₀ ≤ i →
        ShellMink.shellInter (Ac i) (MaxEnv.shell (⋃ j, Ac j) v n c ε) w ⊆
          {z | z + (kk i : ℤ) • vl ∈ Colle35.halfStrip (B i) vl}) :=
  ⟨max i₀ 1, shellObl_pos_max_one i₀, le_max_left i₀ 1,
    shellObl_guard_of_le (le_max_left i₀ 1) hg,
    h ε (max i₀ 1) hε (shellObl_guard_of_le (le_max_left i₀ 1) hg)⟩

/-- **`fillCover` 侧的 `0 < i₀`**（`ChainPartsFeed.lean:343` 的 binder 形）：**种子跟着动**。
⚠ 返回的结论是 `j₀` 处的（种子 `Ac j₀`），**不是** `i₀` 处的——`i₀` 在 `:350` 的残量种子里
出现，这是它与上面两条的唯一区别。见 §1.6 开头的表与消费者说明。 -/
theorem shellObl_fillCover_pos_i₀ {S : Finset (ℤ × ℤ)}
    (h : ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → Env (ShellMink.shellInter (Ac i)
        (MaxEnv.shell (⋃ j, Ac j) v n c ε) w)) →
      ∀ i, max i₀ I₀ ≤ i →
      ShellMink.shellInter (Ac i) (MaxEnv.shell (⋃ j, Ac j) v n c ε) w ⊆
        {z | Colle37.GenClosure S (Ac i ∪
          ShellMink.shellInter (Ac i₀) (MaxEnv.shell (⋃ j, Ac j) v n c ε) w) z})
    (ε i₀ : ℕ) (hε : 0 < ε)
    (hg : ∀ i, i₀ ≤ i → Env (ShellMink.shellInter (Ac i)
      (MaxEnv.shell (⋃ j, Ac j) v n c ε) w)) :
    ∃ j₀ : ℕ, 0 < j₀ ∧ i₀ ≤ j₀ ∧
      (∀ i, j₀ ≤ i → Env (ShellMink.shellInter (Ac i)
        (MaxEnv.shell (⋃ j, Ac j) v n c ε) w)) ∧
      (∀ i, max j₀ I₀ ≤ i →
        ShellMink.shellInter (Ac i) (MaxEnv.shell (⋃ j, Ac j) v n c ε) w ⊆
          {z | Colle37.GenClosure S (Ac i ∪
            ShellMink.shellInter (Ac j₀) (MaxEnv.shell (⋃ j, Ac j) v n c ε) w) z}) :=
  ⟨max i₀ 1, shellObl_pos_max_one i₀, le_max_left i₀ 1,
    shellObl_guard_of_le (le_max_left i₀ 1) hg,
    h ε (max i₀ 1) hε (shellObl_guard_of_le (le_max_left i₀ 1) hg)⟩

end PosI₀

end Nivat.ChainAsm

namespace Nivat.Colle35

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.ChainAsm

variable {α : Type*}

/-! ## §2. `ofPartsInter`: `ChainDataGeom.ofParts` with the shell field swapped -/

/-- **`ChainDataGeom` from its parts, `shell` swapped to `ShellMink.shellInter`.**  Same
binders as `ChainDataGeom.ofParts` (module docstring, `ChainAssemble.lean`) up to the shell
group, which is:

* replaced free derivations — `hhp` alone now gives `subShell`/`shellSubInf` (the latter
  unconditionally); `hfin` plus a new `hsweepW : dot nJ w < 0` gives `shellFinite`;
* a new escape hypothesis `escapeW` (the `w`-analogue of `escape`, additionally demanding the
  escaping point land inside `shellInf ε`) discharging `shellProper`;
* `shellSubStrip`, `shellEnv`, `fillCover` kept as hypotheses, restated against
  `shellInter (Ahat i) (shellInf ε) w` — see the module docstring for why these three are not
  attempted here.

`w` (Collé's `−v_{ℓ_{J+1}}`) is a new parameter: nothing upstream names it. -/
noncomputable def ChainDataGeom.ofPartsInter
    (η xper : Config α) (vl p : ℤ × ℤ) (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ)
    (Env : Set (ℤ × ℤ) → Prop) (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ)
    (envShift : ∀ (v : ℤ × ℤ) (T : Set (ℤ × ℤ)), Env T → Env {z | z + v ∈ T})
    (envB : ∀ i, Env (B i))
    (maxA : ∀ i, IsMaxEnvIn Env (canonA η xper vl B u i) (A i))
    (subBA : ∀ i, B i ⊆ A i) (subAB : ∀ i, A i ⊆ B (i + 1))
    (AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j)
    (vJ1 nJ : ℤ × ℤ) (cJ : ℤ)
    (hsweep : dot nJ vJ1 < 0)
    (hfin : ∀ i, (hatOf A kk vl i).Finite)
    (hhp : ∀ i, hatOf A kk vl i ⊆ halfPlaneGE nJ cJ)
    (hswept : SweptClosed (⋃ i, hatOf A kk vl i) vJ1 nJ cJ)
    (ahat_nonempty : (⋃ i, hatOf A kk vl i).Nonempty)
    (w : ℤ × ℤ) (hsweepW : dot nJ w < 0)
    -- **`I₀`（第 162 轮）**：原文 `b3_colle2.txt:520` 的第二个常数，`:524` 逐字
    -- 「if we consider `i ≥ max{i₀, I₀}`」。此前三条 shell binder 的尾部写成 `∀ i, i₀ ≤ i →`，
    -- 比 `:524` 强（原文从不主张 `I₀ ≤ i₀`），按硬规矩 5 属于我们加的量词。见
    -- `ChainData.I₀`（`Lemma35.lean`）的完整对齐说明。守卫仍锚在 `i₀`，不抬到 `max`。
    (I₀ : ℕ)
    -- **Round 159 guard**, same reason as `fillCover` below: `escapeW` only ever feeds
    -- `ChainData.shellProper`, whose paper sentence (`b3_colle2.txt:530`) sits under `:516`'s
    -- "for an appropriate `ε ∈ ℕ` fixed and all `i` sufficiently large".  The old `∀ i ε` was
    -- ours.  Free at the only consumer (`Lemma35.lean`'s `hfail`: `hεpos`, `hEnv` and
    -- `hi₀i : i₀ ≤ σ j` are all in scope there before `shellProper` is applied), and the floor
    -- is what the `faceStart`-pinning route needs (`tmp/wip/lane-tower-hlev-escapew.lean`
    -- `escapeW_of_overshoot`'s `hstart`, only available for `i ≥ i₀` via `hgJspec`).
    (escapeW : ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → Env (ShellMink.shellInter (hatOf A kk vl i)
        (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w)) →
      ∀ i, max i₀ I₀ ≤ i → ∃ g ∈ hatOf A kk vl i, ∃ t : ℕ,
      g + (t : ℤ) • w ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε ∧
      g + (t : ℤ) • w ∉ hatOf A kk vl i)
    (shellSubStrip : ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → Env (ShellMink.shellInter (hatOf A kk vl i)
        (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w)) →
      ∀ i, max i₀ I₀ ≤ i →
      ShellMink.shellInter (hatOf A kk vl i)
          (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w ⊆
        {z | z + (kk i : ℤ) • vl ∈ Colle35.halfStrip (B i) vl})
    (shellEnv : ∃ ε i₀, 0 < ε ∧ ∀ i, i₀ ≤ i →
      Env (ShellMink.shellInter (hatOf A kk vl i)
        (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w))
    -- **Round 81 weakening.**  This binder used to ask the producer for the *single-generator*
    -- `⋃ n, genFill S gen …` shape, which `tmp/wip/lane-cd-cw-fillcover-refute.lean`
    -- (`not_fillCover_at_a'`, `:422`) kernel-refutes at `(i, i₀, ε) = (2, 0, 5)` on the
    -- `ApexUnique.Shex` instance — and `not_fillCover_at_a` refutes the mirror choice
    -- `gen = F.a`, so *no* single generator discharges it.  Collé never picks a generator:
    -- `IsGeneratingSet` (`Generating.lean:58`, `b3_colle2.txt:271`) quantifies over **every**
    -- vertex `a ∈ S` with `LatticeConvex (S.erase a)`, which is exactly `Colle37.GenClosure`
    -- (`GenClosureDef.lean:26`).  The added quantifier was ours, so per 硬规矩 5 it is deleted
    -- here rather than discharged.  The field below is *already* phrased against `GenClosure`
    -- (`Lemma35.lean:778`, Round 80), so this binder now matches its consumer verbatim and the
    -- `genFill_subset_genClosure` weakening step is no longer needed.  Nothing is lost: the old
    -- binder implies this one through that same bridge.
    -- **Round 159 guard.**  The remaining `∀ ε` was also ours.  It is kernel-refuted by
    -- `Nivat.LaneLeafAGenInter.not_fillCover_binder_exh`
    -- (`tmp/wip/lane-leafa-gen-fillcover-inter.lean:746`; integrator re-ran `check1.sh`
    -- EXIT=0, axioms all whitelist) at `(i, i₀, ε) = (2, 0, 5)` on the `ApexUnique.Shex`
    -- instance, with `hexh` and the whole `nℓ`-group discharged on the same assignment —
    -- while the *same* instance satisfies the conclusion at the `(ε, i₀) = (1, 0)` that its
    -- own `shellEnv` produces (`fillCover_guarded_x`, same file `:639`).  Paper `:530` lives
    -- entirely under `:516`'s "for an appropriate `ε ∈ ℕ` **fixed** and all `i` sufficiently
    -- large", so the guard below is the paper's own quantifier, not an extra hypothesis.
    (fillCover : ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → Env (ShellMink.shellInter (hatOf A kk vl i)
        (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w)) →
      ∀ i, max i₀ I₀ ≤ i →
      ShellMink.shellInter (hatOf A kk vl i)
          (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w ⊆
        {z | Colle37.GenClosure S (hatOf A kk vl i ∪
          ShellMink.shellInter (hatOf A kk vl i₀)
            (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w) z})
    (vJ : ℤ × ℤ) (F : FaceBlock S nJ vJ)
    -- **The generating point is the `v_J`-forward end of the face** (2026-09-19, team-lead
    -- ruling; carried over from `ofParts` unchanged — see `tmp/wip/shell_aenvfix_fillCover_wit
    -- .lean` for the `gen = (1,0) = a'` vs. `gen = (0,0) = a` split on this very `shellInter`
    -- object).
    (gen_eq : gen = F.a')
    (vJ_prim : Primitive vJ) (nJ_prim : Primitive nJ)
    (bottom : ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ reachSet (⋃ i, hatOf A kk vl i) vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k →
        z₀ + k • vJ + (b - F.a) ∈ reachSet (⋃ i, hatOf A kk vl i) vJ1) ∧
      (∀ z ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ (ε + 1),
        z ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε ∨
          ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ))
    (rec_p : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + p ∈ ⋃ i, hatOf A kk vl i)
    (dot_nJ_p : dot nJ p ≠ 0)
    (rec_vJ : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + vJ ∈ ⋃ i, hatOf A kk vl i)
    (cL : ℤ)
    (ahat_halfPlane_L : ∀ g ∈ ⋃ i, hatOf A kk vl i, cL ≤ dot (det p vJ • (-p.2, p.1)) g)
    (ahat_attained_L : ∃ g ∈ ⋃ i, hatOf A kk vl i, dot (det p vJ • (-p.2, p.1)) g = cL)
    (nfp_L : ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
      PeriodicOnWith xper {z | cL ≤ dot (det p vJ • (-p.2, p.1)) z} h ∧
      PeriodicOnWith xper {z | cL ≤ dot (det p vJ • (-p.2, p.1)) z} h') :
    ChainDataGeom η xper vl p S gen where
  Env := Env
  B := B
  A := A
  u := u
  kk := kk
  Ahat := hatOf A kk vl
  shell := fun i ε =>
    ShellMink.shellInter (hatOf A kk vl i) (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w
  shellInf := fun ε => MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε
  fill := fun i i₀ ε => genFill S gen (hatOf A kk vl i ∪
    ShellMink.shellInter (hatOf A kk vl i₀)
      (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w)
  envB := envB
  envA := envA_of_max maxA
  subBA := subBA
  subAB := subAB
  subStrip := subStrip_of_max maxA
  agreeA := agreeA_of_max maxA
  AhatEq := fun i => hatOf_eq i
  AhatMono := AhatMono
  maximalHat := maximalHat_of_max envShift maxA
  shellFinite := fun i ε => shellInterFinite_of hfin hsweepW i ε
  subShell := fun i ε => subShellInter_of hhp w i ε
  shellSubInf := fun i ε => shellSubInfInter_of w i ε
  shellInfZero := shellInfZero_of (Set.iUnion_subset hhp) hswept
  I₀ := I₀
  shellSubStrip := shellSubStrip
  shellProper := fun ε i₀ hε hEnv i hi => by
    obtain ⟨g, hg, t, hin, hout⟩ := escapeW ε i₀ hε hEnv i hi
    exact shellProperInter_of hg hin hout
  shellEnv := shellEnv
  fillZero := fun i i₀ ε => subset_rfl
  fillStep := by
    subst gen_eq
    exact fun i i₀ ε m z hz => genFill_step S F.a' _ m z hz
  -- Round 81: the binder is now stated in the field's own `Colle37.GenClosure` shape
  -- (see the note at the `fillCover` binder), so the `genFill_subset_genClosure` weakening
  -- that used to sit here is gone and the hypothesis passes straight through.
  fillCover := fillCover
  vJ1 := vJ1
  nJ := nJ
  cJ := cJ
  shellInf_eq := fun _ => rfl
  ahat_nonempty := ahat_nonempty
  ahat_halfPlane := fun g hg => Set.iUnion_subset hhp hg
  vJ := vJ
  a := F.a
  a' := F.a'
  r := F.r
  latticeConvex_S := F.latticeConvex_S
  a_mem := F.a_mem
  a'_mem := F.a'_mem
  lex := F.lex
  lex' := F.lex'
  edge := F.edge
  edge' := F.edge'
  dot_nJ_vJ := F.dot_nJ_vJ
  bottom := bottom
  rec_p := rec_p
  dot_nJ_p := dot_nJ_p
  vJ_ne := vJ_prim.ne_zero
  vJ_prim := vJ_prim
  rec_vJ := rec_vJ
  cL := cL
  ahat_halfPlane_L := ahat_halfPlane_L
  ahat_attained_L := ahat_attained_L
  nJ_prim := nJ_prim
  nfp_L := nfp_L

end Nivat.Colle35

#print axioms Nivat.ChainAsm.shellInter_subset_shell
#print axioms Nivat.ChainAsm.shellInterFinite_of
#print axioms Nivat.ChainAsm.subShellInter_of
#print axioms Nivat.ChainAsm.shellSubInfInter_of
#print axioms Nivat.ChainAsm.shellProperInter_of
#print axioms Nivat.ChainAsm.shellSupB_free
#print axioms Nivat.ChainAsm.shellSupB_field_free
#print axioms Nivat.ChainAsm.shellSandwich_520
#print axioms Nivat.ChainAsm.shellObl_pos_max_one
#print axioms Nivat.ChainAsm.shellObl_guard_of_le
#print axioms Nivat.ChainAsm.shellObl_escapeW_pos_i₀
#print axioms Nivat.ChainAsm.shellObl_shellSubStrip_pos_i₀
#print axioms Nivat.ChainAsm.shellObl_fillCover_pos_i₀
#print axioms Nivat.Colle35.ChainDataGeom.ofPartsInter
