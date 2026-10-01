/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Nivat.Section8.ExternalDefs
import Nivat.External.Colle.Lemma35
import Nivat.External.Colle.Lemma45
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.CaseSplit
import Nivat.External.Colle.Step_BiONED
import Nivat.External.Colle.Step_Nonempty
import Nivat.External.Colle.ChainGeom
import Nivat.External.Colle.Prop210
import Nivat.External.Colle.DecompData
import Nivat.External.Colle.Lemma41
import Nivat.External.Colle.PeriodTransport
import Nivat.External.Colle.Claim47Core
import Nivat.External.Colle.L1Data
import Nivat.External.Colle.L1Assemble
import Nivat.External.Colle.L1Claim
import Nivat.External.Colle.RegionClaim411
import Nivat.External.Colle.L3Band
import Nivat.External.Colle.C11Bridge
import Nivat.External.Colle.HalfPlaneDoublyPeriodic
import Nivat.External.Colle.L1SweepBridge
import Nivat.External.Colle.ChainPartsFeed
import Nivat.External.Colle.ChainKK
-- 2026-09-21 接链（硬规矩 9），leaf A 侧：`ItemIIChain` 是 Collé item (ii)（`b3_colle2.txt:474`）
-- 那条**唯一剩下的逃生阀**的生产者。`exists_itemII_chain`（`ItemIIChain.lean:117`）从 `Case2`
-- 与 `𝒮_φ` 的边法向造出链 `(B, A, u)`，`not_hchain_of_exists_itemII_chain`（`:181`）在内核里
-- 证明该链**不满足** `ChainDataGeom.false_of_chain_halfStrip` 的前提 —— 即它与
-- `ChainRecursion.chainB` 那条已被证伪的链不是同一个对象；`chainDataGeomParts_of_chain`（`:212`）
-- 把它接成 `ChainAsm.Aparts.ChainDataGeomParts`。消费者是本文件 `exists_chainData`（`:1065`）。
-- ⚠ 这一步**还没有**关掉那条 `sorry`：`Parts → ChainDataGeom` 的 smart constructor
-- 2026-09-20 因依赖 `sorryAx` 被删，差额是 `ofParts` 的第 25 条前提 `rec_vJ`（已派 Pbridge 重建）。
-- 盲区 1b 实测（`tmp/ambig_scan2.py`，在 `tmp/`，未落地）：连同下面的 `ConeStepIn`，
-- 新进 `RegionSteps` 闭包 **3 个**模块，下游 11 个模块重名冲突 **0 条**。
import Nivat.External.Colle.ItemIIChain
-- 2026-09-21 接链（硬规矩 9）：`ConeStepIn` 把 `hstepIn` 的内容归约到 `B` 在 `nℓ` 上的**层占据**
-- （`exists_level_of_stepIn`，`ConeStepIn.lean:121`），消费者是本文件 `:2551` 的 `hstrip`。
import Nivat.External.Colle.ConeStepIn
import Nivat.External.Colle.L1CoverBridge
-- 2026-09-21 接链（硬规矩 9）：`CutLevels` 是原文 `b3_colle2.txt:816` 的 `0 = d₀ < d₁ < ⋯`
-- （**已取到**的距离序列）的存在性。`exists_lev_for_ofCut`（`CutLevels.lean:97`）从
-- 「`b₀` 层被取到」＋「`dot m` 在 `Rinf` 上向下无界」两条直接产出
-- `L1Region.ofCut`（`L1Region.lean:240`）所要的 `hlev` / `hexh` / `hgap` 三条。
-- 消费者是本文件 `:1521` 的 `exists_cutResidualR_of_claim46`，即
-- `L1Claim.CutResidualR`（`L1Claim.lean` §5）的同名三个字段；它上游只有 `L1Region`
-- （已在本文件闭包内，经 `L1Claim`），不引入新的下游闭包。
import Nivat.External.Colle.CutLevels
-- 2026-09-21 接链（硬规矩 9）：`TowerIndex` 是原文 `b3_colle2.txt:812-814`「取最小的 `I` 使
-- `(T^u η)|𝓡_I` 仍以 `h` 为周期」的生产者。指标在我们这边是翻过来的：`R 0` = 塔底 `𝓡_{ι−1}`
-- （`:806`，`h` 在其上是周期），`R M` = 塔顶（`:810` 的 Proposition 2.12 给不周期）。
-- `exists_last_periodOn_finite`（`TowerIndex.lean:46`）产出 `I < M` 使 `R I` 周期、`R (I+1)` 不周期。
-- 消费者是本文件 `:1521` 的 `exists_cutResidualR_of_claim46`：`Rinf := R (I+1)` 付 `hinf`，
-- `R I ⊇ cut Rinf m lev 0` 经 `periodOn_of_le_last` / `PeriodOn.mono` 付 `hbase`。
-- 它只 import `L1Region`（已在本文件闭包内），不引入新的下游闭包。
import Nivat.External.Colle.TowerIndex
-- 2026-09-23 接链（第一百五十七轮，lane-towerpkg / lane-tower-hbase / lane-tower-hlev）：
-- `LaneTowerPkgMain.lane_towerpkg_package`（`TowerPkgMain.lean:1014`）的结论与本文件
-- `exists_cutResidualR_of_claim46` 里塔包那条 `obtain` 的 11 条合取逐字符相同，binder 取自本
-- 定理已有的那组（去掉塔包用不到的 `hgen`/`S`/`gen`），0 sorry、公理白名单。原文 `:806-820`。
import Nivat.External.Colle.TowerPkgMain
import Nivat.External.Colle.SweepCriterion
import Nivat.External.Colle.WindowPlace
-- 2026-09-21 接链（硬规矩 9）：`TailLevels.htail_of_levels`（`TailLevels.lean:71`）是
-- `WindowPlace.exists_tau_mem_cut`（`WindowPlace.lean:34-35`）那条 `htail` 形参的生产者，
-- 把它归约成 Figure 2（`b3_colle2.txt:396-398`）的两条半无穷边 `hray` / `hlevel`。
-- 消费者是本文件 `:1607` 的 `exists_cutResidualR_of_claim46`，经 `exists_tau_mem_cut_pair`。
-- ⚠ 读法限定：`Rinf` 在链上是 `coneRegion B vl u' = B + ℕvl + ℕu'`（`ConeRegion.lean:68`，
-- 原文 `:780`），**不是** `wedgeFull B vl u' = B + ℤ•vl + ℕu'`（`L1RegionBuild.lean:230`）；
-- `hbase₁`（`:1601`）正是在 `coneRegion` 上陈述的，换成 `ℤ•vl` 版即违反硬规矩 7。
import Nivat.External.Colle.TailLevels
-- `htail_of_levels`（`TailLevels.lean:71`）的 `hlevel` 形参的生产者：
-- `Nivat.LevelHit.hlevel_of_coneRegion`（`LevelHit.lean:40`，`[propext, Quot.sound]`）。
-- 原文 `:396-398` Figure 2 的第二条半无穷边：`coneRegion B vl u' = B + ℕvl + ℕu'`
-- 在 `dot m vl = 1` 下每一层都被取到，取 `z₀ := b₀ + (b − dot m b₀) • vl`。
import Nivat.External.Colle.LevelHit
-- 2026-09-21 接链（硬规矩 9）：`StripDescend` 把洞 6 的 `hstrip`（本文件 `:2640`）**无角点**地
-- 归约成 `hplaceB`（`b3_colle2.txt:798` Figure 10）＋ `hdown`（`:794-796` 的逐行归纳）两条；
-- `place_of_down`（`StripDescend.lean:151`）再把 `hplaceB` 的「向下」一半由 `hdown` 免费推出。
-- `StripPlace` 是同一洞的角点写法，其 `hBcorner` 前提链上无生产者，留作对照。
import Nivat.External.Colle.StripPlace
import Nivat.External.Colle.StripDescend
-- 2026-09-21 接链（硬规矩 9）：leaf A 的三条新件，消费者一律是本文件 `:1079` 的
-- `exists_chainData`。三条都在 `exists_itemII_chain` 的**上游或同层**，不引入新的下游闭包
-- （`AGlue` 只加 `ONEDRational`/`SfinBound`，两者已在 `ItemIIChain` 闭包内）。
-- `AGlue`：`hnℓ'` 与 `hdet hn hn' hm hm'` 两组实参的生产者。
-- `RecVJ`：`ChainDataGeom.ofParts` 第 25 条前提 `rec_vJ` 的生产者，经半平面恒等式。
-- `PartsToGeom`：24 字段 → `ChainDataGeom` 的诚实 24+1 构造器，`rec_vJ` 留显式参数。
import Nivat.External.Colle.AGlue
import Nivat.External.Colle.RecVJ
import Nivat.External.Colle.PartsToGeom
-- **2026-09-20 接链（`CLAUDE.md` 硬规矩 9），L1 侧.**  两条生产者此前都在链外（`onchain.py`
-- 口径 "UP"，即 `RegionSteps` 随时可以 import，只是从来没人做这个动作）：
-- `StrictWindow.hbase_of_cone_halfStrip_of_hmono` 造 `hbase`，
-- `WedgeAssemble.nonempty_wedgeResidualR_of_hbase_at_shear` 把 `hbase` 变成
-- `Nonempty (WedgeResidualR ξ S vl)` —— 正是 `exists_wedgeResidualR`（`:1195`）的结论。
-- 受影响集合已先算（盲区 1b）：`RegionSteps` 的下游 11 个模块，本次新进闭包的模块 6 个，
-- 同名不同命名空间且两边都 `open` 的候选 0 个（`tmp/ambig_scan.py`，在 `tmp/`，未落地）。
import Nivat.External.Colle.StrictWindow
import Nivat.External.Colle.WedgeAssemble
-- 2026-09-20 接链（硬规矩 9）：`EnvFit` 是 `hmono` 的唯一生产者
-- （`EnvFit.exists_shear_hmono_of_edges` / `_of_enveloped`）。
-- 加 import 前按盲区 1b 实测：`EnvFit` 不 import `RegionSteps`（无环），
-- 新进入 `RegionSteps` 闭包的模块 **1 个**（就是 `EnvFit` 自己），
-- `tmp/ambig_scan.py` 对 11 个下游模块扫描重名 **0 条**（在 `tmp/`，未落地）。
import Nivat.External.Colle.EnvFit
import Nivat.External.Colle.ConeStepWin
-- 2026-09-20 接链（硬规矩 9）：`VlMinAdj.vlmin_of_adjacent` 是 `hvlmin` 的生产者
-- （洞 4 / 5 / 6 的共同残余）。盲区 1b 实测：新进闭包 2 个模块（`VlMinAdj`、
-- `CornerAdjClash`），`tmp/ambig_scan.py` 对下游扫描重名 0 条（在 `tmp/`，未落地）。
import Nivat.External.Colle.VlMinAdj
-- 2026-09-20 接链（硬规矩 9）：`PhiIotaWindow.exists_window_strict_of_index` 是洞 3 的生产者。
-- 盲区 1b 实测：新进闭包 1 个模块（`PhiIotaWindow`），`tmp/ambig_scan.py` 重名 0 条（在 `tmp/`，未落地）。
import Nivat.External.Colle.PhiIotaWindow
-- 2026-09-20 接链（硬规矩 9）：`Stage2Index.exists_greatest_periodOn_chainFull` 是
-- `:820`「取最大的 `N` 使 `(T^u η)|𝓡^N_I` 仍以 `h` 为周期」的生产者，消费者是本文件的
-- `exists_stage2_frame_of_claim46`（见该定理的 `obtain ... := sorry` 之后一行）。
-- 🔴 **2026-09-21 订正**：该消费者已随换框退役（`OPEN.md #21`），本 import 目前**无消费者**。
-- 不删是因为 `:820`「取最大的 `N`」这一步在新框里照样要用，只是要换成
-- `L1Region.exists_greatest_periodOn` 作用在 `L1Region.cut` 上（`exists_L1MaxBResidual_of_cutResidualR`
-- 已经这么做了，`L1Claim.lean` §5）。下一个动作是判定 `Stage2Index` 是否还有用，没用就摘掉这条 import。
-- 盲区 1b 实测：`Stage2Index` 只 import `L1RegionBuild` / `L1Region`，两者已在
-- `RegionSteps` 闭包内，故新进闭包 **1 个**（`Stage2Index` 自己）；
-- 它声明的两个名字在 `Nivat/` 下全局 grep **0 条**重名。
import Nivat.External.Colle.Stage2Index
import Nivat.External.Colle.NewtonZonotopeMod
-- **接链 2026-09-21（硬规矩 9）**：`EnvSuperset` 供给 Collé item (ii)（`b3_colle2.txt:474-476`）
-- 的存在性，见 `exists_chainData` 的 docstring 末节「item (ii) 的生产者」。
import Nivat.External.Colle.EnvSuperset
-- 2026-09-21 接链：洞 6 的 `hsupp` 要把窗口一侧算成闭形式（`relSuppVal_zonoF` /
-- `eq_zonoArgmin_of_strict` / `suppVal_congr_of_Conv_eq`）。`WindowFit` 在此之前
-- **只被 `All.lean` import**，是滞留 32 个里的一个；盲区 1b 实测：它只 import
-- `EnvTranslate / PhiIotaWindow / NewtonZonotope / LatticeEdges / ConeRegion /
-- VertexFromEdge`，六个全都已在本文件闭包内，不引入新的下游闭包。
import Nivat.External.Colle.WindowFit
-- 2026-09-22 接链（硬规矩 9）：Figure 11(B) 的生成集包 `L1GenPackage.exists_gen_package`
-- （原文 `:848/:856`），消费者是本文件 `exists_cutResidualR_of_claim46`（`Sφ a hgen` 三个 binder）。
-- 它只 import `DecompData`/`HalfPlaneShells`（均在本文件闭包内），不引入新的下游闭包。
import Nivat.External.Colle.L1GenPackage
import Nivat.External.Colle.L1LinePackage
import Nivat.External.Colle.L1LineEdgePackage
import Nivat.External.Colle.LineGenIndex
import Nivat.External.Colle.HsuppAssemble
import Nivat.External.Colle.HstepAll
import Nivat.External.Colle.ConeRecession
import Nivat.External.Colle.Hole3Room
import Nivat.External.Colle.NlmaxReduce
-- 第 192 轮：`hstrict` 的等价判据（lane-tower-hlev）。传递地带进 `RegionNlDict` /
-- `ZonoNormalPair` / `ZonoWadjCrit` / `NormalCycle*` 共 7 个模块，全部 0 `sorry`、公理全白
-- （集成者按盲区 2 先算受影响集合：`RegionSteps` 闭包 229 → 236，无环）。
import Nivat.External.Colle.FanOrderCriterion
-- 第 210 轮：`exists_itemII_recursion` 的两条缺失 binder（lane-tower-hlev）＋「本 `theorem` 的
-- binder 足以调用它」的收据（集成者）。带进闭包只为硬规矩 9——⛔ **它不关下面的 `sorry`**：
-- 那条 `∃ _rd : ItemIIRecursionData …, True` 不是 `ChainDataGeom`，shell 块 / `bottom` / `rec_p`
-- 都不是它的字段（见 `ItemIIFeed.lean` 头部的 ⚠ 段）。
import Nivat.External.Colle.ItemIIFeed
-- 2026-09-26（hole2-ctx）：`HsuppContain.hcont`（Minkowski 平移，0 sorry、公理全白）供
-- `Hole2Room.sphi_shift_subset`。`HsuppContain` 不 import `RegionSteps`（`tmp/wip/hole2-importclosure.py` 实测），无环。
import Nivat.External.Colle.HsuppContain
import Nivat.External.Colle.Hole1PushShell

/-!
# The read-off steps of `colle_region`

**Status 2026-09-30: every step in this file is proved.**  The last open leaf,
`exists_chainData`, now `exact`s `Nivat.ColleReg.exists_chainData_closed`
(`Hole1PushShell.lean`); measured that day, `bash scripts/sorries.sh` reports `TOTAL: 0` and
`#print axioms Nivat.nivat_conjecture` reports `[propext, Classical.choice, Quot.sound]`.
Everything below that speaks of open leaves, `sorry`s or `sorryAx` is dated history, kept for
the record; re-run the scripts rather than reading status off this docstring.

`Nivat.ColleReg.colle_region` (`ColleRegion.lean`) was one proof containing seven `sorry`s.
That shape cannot be worked on by more than one person at a time, because every hole lives
inside the same tactic block.  This file holds all of them as named theorems, so each can be
attacked independently and each has an address the blueprint can point at.

Seven holes became six theorems.  Two of the original seven were **not** well posed once
separated, and the separation is what exposed that; see "Joints that do not close" below.

## The contract on these signatures

Each theorem below takes exactly the hypotheses that were in scope at the corresponding
`sorry` inside `colle_region` (the one documented exception is `hdet_ℓ`, joint 1).  So each
is provable if and only if that `sorry` was dischargeable at that point, and `colle_region`
type-checks by applying them in order.

Consequently:

* **Adding a hypothesis that was not in scope at the hole is forbidden.**  It would make the
  theorem too weak to close the hole it was extracted from, and `colle_region` would stop
  compiling.
* **Restoring a hypothesis that *was* in scope at the hole is allowed and sometimes
  mandatory** — see "`hξ` restored" below.  `colle_region` has it and can pass it, so nothing
  downstream moves.
* **Dropping an unused hypothesis is allowed** — that strengthens the statement, and the
  call sites keep working.  But see below: it is exactly what broke two of these six.
* **Weakening a conclusion is forbidden**, for the same reason as adding an out-of-scope
  hypothesis.

## `hξ` restored, 2026-09-16 (r67 verdict)

The extraction dropped `hξ : IsMinimalCounterexample ξ` from every step whose `sorry` did not
visibly use it.  For two of them that overshot into falsehood, and both are refuted
kernel-clean in the tree:

| step | refutation | witness `ξ` | why `hξ` excludes it |
|---|---|---|---|
| `region_periods_and_rays` | `ColleStep.not_region_periods_and_rays` (`Step_PeriodsRays.lean:556`) | `[0 < z.2]` | periodic, and `ξ (0,0) = 0` |
| `region_periods_and_rays` (`ChainDataGeom` form, 2026-09-18) | `ColleStep.PeriodsRays2.not_RPRStatement` (`Step_PeriodsRays2.lean`) | `z.1 + [z.2 < 0]` | infinite range |
| `region_not_periodic` | `ColleStep.region_not_periodic_refuted_strong` (`Step_NotPeriodic.lean:430`) | `[0 ≤ z.1] + [0 ≤ z.2]` | `ξ (-1,-1) = 0` |

**Superseded 2026-09-17.**  Both steps now take a `ChainDataGeom` instead of a bare
`ChainData`, and both dropped `hξ` again — this time soundly, because the discriminating
hypothesis is no longer minimality but the region geometry.  Each refutation witness has a
region with only one recession direction (`Step_PeriodsRays.lean:141-147`:
`Â_∞ = [0,∞) × [0,1]`), so neither can carry a `ChainDataGeom`; see the docstrings of the two
theorems for the field that fails.

(The 2026-09-16 reading of these two witnesses was that they fail the positivity clause
`∀ z, 0 < ξ z` of `IsCounterexample` (`Section8/ExternalDefs.lean:49`), which is true and
measured — closure `[propext, Classical.choice, Quot.sound]` on both refutations and on
`PeriodsRays.cx_not_minimalCounterexample` (`:477`) and `xiD_not_minimalCounterexample`,
`scripts/check_r67_verdict.lean`.  It was simply not the cheapest way out: restoring `hξ`
excludes the witnesses but supplies nothing a proof can use, which is why both steps stayed
open for a day and then closed the moment the region geometry was named instead.)

`hξ` is therefore off both signatures again, and both are now proved.  `region_latticeConvex`
still takes it and still uses it.  The refutations stand against the stripped bare-`ChainData`
statements and are kept for that.

**Superseded again 2026-09-18, for `region_periods_and_rays` only.**  The "soundly" above
held for `region_not_periodic` (proved) but not for `region_periods_and_rays` (still `sorry`,
so its "unused" was never linted).  `ColleStep.PeriodsRays2.not_RPRStatement`
(`Step_PeriodsRays2.lean`) refutes the `ChainDataGeom` form kernel-clean with a first-quadrant
region and `ξ z = z.1 + [z.2 < 0]` — infinite range, so `hξ` excludes it, and this time `hξ`
*is* what a proof needs: `Colle41.lemma41_of_sweep` (`Lemma41.lean:703`) starts with
`(Set.range η).Finite` and `x ∈ orbitClosure η`.  `hξ` and `hϑ_mem` are back on that
signature; see its docstring.

## Joints that do not close

Extraction surfaced two places where the surrounding proof never connects the objects it
hands on.

1. **`ℓ` was never tied to `vl`.**  The direction `ℓ` comes from the Claim 4.6 step; the
   chain direction `vl` comes from the chain-data step.  Nothing in `colle_region` asserted
   they are related, yet the argument of Collé runs the chain along the line `ℓ` — his
   notation for the chain direction is literally `v_ℓ`.  This is now repaired, deliberately
   and in the direction that makes more work rather than less: since 2026-09-17
   `exists_preamble` is *required to produce* `Nivat.LE2.dot ℓ vl = 0`, and
   `exists_chainData` / `region_case1` may assume it.  The alternative — leaving the two
   unrelated — would have left the period steps unprovable.

   **Corrected 2026-09-17: the conjunct used to be `det ℓ vl = 0`, which is the wrong
   relation.**  In Lean `ℓ` is the *normal* of the nonexpansive line, not its direction:
   `Colle45.IsOneSidedNonexpansive ξ ℓ` is `∀ z, dot ℓ z ≤ 0 → x z = y z`
   (`Lemma45.lean:95-97`), and `Colle45.NonExpansiveLine` goes through
   `halfPlaneLE ℓ 0 = {z | dot ℓ z ≤ 0}` (`Lemma45.lean:85-87`, `LatticeEdges.lean:1757`);
   `Step_BiONED.lean:158-168` builds `ℓ` as the primitive vector *parallel to the real normal
   `w`*.  So the line is `{dot ℓ · = 0}` and the `v_ℓ` of Collé satisfies `dot ℓ v_ℓ = 0`,
   whereas `det ℓ vl = 0` says `vl ∥ ℓ`, i.e. `vl` along the normal, perpendicular to `v_ℓ`.
   The two readings are incompatible for nonzero vectors — `det_ne_zero_of_dot_eq_zero`
   below is the compiled record — and the route of Collé to the period (Propositions 2.10
   and 2.12) returns a `u` with `dot ℓ u = 0`, so under the `det` reading `exists_preamble`
   could not be closed; under the `dot` reading it is.  The symptom had been written down
   before the cause: `Step_PeriodsRays.lean:70-72` notes that `hdet_ℓ` forces the `ℓ` of its
   witness to be *vertical* for a horizontal nonexpansive line.  A witness that has to be
   contorted to satisfy a hypothesis is evidence against the hypothesis, not a curiosity of
   the witness.  See `blueprint/NOTE.md` 「已裁决：`exists_preamble` 的 `det ℓ vl = 0` 应为
   `dot ℓ vl = 0` — 2026-09-17」.

2. **The second period was not required to lie in the recession cone.**  The original proof
   produced `h, h'` in one `sorry` and then asked a *separate* `sorry` for base points
   `z₀, z₀'` whose forward rays stay in the region.  For an arbitrary pair `h, h'` no such
   base points exist, so that second statement was false as posed in isolation.  The two are
   merged below into `region_periods_and_rays`, which produces periods and rays together —
   which is also what the source does (the periods run along the two unbounded edges).

3. **`shellInf` was opaque, so Claim 3.7 could not be reached.**  `ChainData.shellInf` is
   constrained only by three containment fields; Collé gives it by a formula
   (`b3_colle2.txt:440`).  Without the formula `Nivat.Colle37.claim37`'s `reach` obligation is
   not merely unproved but *false* over `ChainData` — `Nivat.Colle35.nonempty_chainData` has
   `shellInf 0 = {0}` and `shellInf 1 = {0, (1,0)}`, and no translation carries `(1,0)` into
   `{0}`.  Repaired on 2026-09-17 the same way as joint 1, by asking `exists_chainData` for
   more: it now produces a `Nivat.Colle35.ChainDataGeom` (`ChainGeom.lean`), which extends
   `ChainData` with the shell formula and with the geometry of the `ℓ_J`-edge.  Each added
   field is a statement Collé asserts outright in §3, and `region_not_periodic` became a
   theorem.  `ChainData` itself is untouched, per CLAUDE.md 「定义修法：加强，不替换」.

4. **Where the second period of `ϑ` comes from.**  Lemma 3.5 hands
   `region_periods_and_rays` a *single* period `p`, and the step has to produce two
   independent ones.  It is **not** `x_per`'s full periodicity: that sentence
   (`b3_colle2.txt:539`) sits under the §3.1 contradiction hypothesis `b3_colle2.txt:537`
   (*"as `−ℓ ∉ nexpd(η)` or `ℓ ∉ nexpd(η)` for all lines"*), which `exists_chainData`'s own
   `hw₁ : w ∈ ONED ξ`, `hw₂ : -w ∈ ONED ξ` negate; and §4 Case 2, the branch this chain
   lives in, assumes the opposite outright (`b3_colle2.txt:890`, *"we may assume that
   `x_per|ℋ(ℓ^(−))` is not fully periodic"*).  Collé's actual source is `b3_colle2.txt:904`:
   Claim 4.11 + Lemma 4.1 give a **sub**region `𝒦 ⊂ Â_∞^{(ε)}` carrying both periods —
   on `Â_∞^{(ε)}` itself `ϑ` has only the one parallel to `−ℓ` (`b3_colle2.txt:900`).
   `region_periods_and_rays` was rewritten accordingly on 2026-09-17 to conclude
   `∃ R ⊆ Â_∞`, and is open.  See `blueprint/NOTE.md` 「`DoublyPeriodic xper` 第三次入侵」.

## Status

**Measured 2026-09-17** (third measurement of the day: after the `DoublyPeriodic xper`
retraction, and after the Lemma 4.5 case split was restored) from `bash scripts/sorries.sh`
plus `#print axioms` on each step (`tmp/assembly_axioms.lean`).  Seven are closed; three
remain (`exists_preamble` closed later on 2026-09-17; its row was re-measured then).

| theorem | own body | measured closure |
|---|---|---|
| `exists_biONED_direction` | **proved** --- `Step_BiONED.lean` | `[propext, Classical.choice, Quot.sound]` |
| `region_nonempty` | **proved** --- `Step_Nonempty.lean` | `[propext, Classical.choice, Quot.sound]` |
| `region_latticeConvex` | **proved** --- no `sorry` in this file | `[propext, Classical.choice, Quot.sound]` |
| `region_not_periodic` | **proved** --- `ChainGeom.lean` | `[propext, Classical.choice, Quot.sound]` |
| `not_case2_of_case1` | **proved** --- in this file | `[propext, Classical.choice, Quot.sound]` |
| `case1_of_not_case2` | **proved** --- in this file | `[propext, Classical.choice, Quot.sound]` |
| `exists_preamble` | **proved** --- in this file, 2026-09-17 | `[propext, Classical.choice, Quot.sound]` |
| `exists_chainData` | `sorry` --- now Case 2 only | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `region_case1` | `sorry` --- new 2026-09-17 | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `region_periods_and_rays` | `sorry` --- reopened, scope corrected | `[propext, sorryAx, Classical.choice, Quot.sound]` |

The count went 2 → 4 on 2026-09-17.  That is not a regression: `exists_chainData` had been
asserting Collé's **Case 2** output (`b3_colle2.txt:758`) with no hypothesis, and `:760` says
Case 1 takes a different route entirely.  `exists_preamble` and `region_case1` are the two
pieces that were hidden inside that over-strong statement.  See `blueprint/NOTE.md`
「`exists_chainData` 吞掉了 Lemma 4.5 的 Case 2 前提」.  `exists_preamble` was closed later the
same day, so the live count is three.

The closed ones are **aliases** for theorems proved in their own files, which is how
parallel worktrees avoid colliding on this one: each agent writes a new file and
nobody but the integrator edits this one.  For the two produced by `rfl`-substitution the
identity `@Nivat.ColleReg.X = @Nivat.ColleStep.X` was checked to elaborate by `rfl`, which
fails unless the two types are defeq, so no hypothesis was added and no conclusion weakened.

`colle_region` itself contains no `sorry`: it is pure assembly, so every hole in it has a name
that the blueprint can point at.

## How this file reaches `Nivat.nivat_conjecture` (measured 2026-09-18)

Through a real dependency edge, since 2026-09-18: `Nivat/Section8/ExternalDischarged.lean`'s
`exists_fullyPeriodic_region'` calls `Nivat.ColleReg.colle_region` (`ColleRegion.lean`), which
is assembly over the theorems of this file, and `FirstHalfPlane.lean` calls
`exists_fullyPeriodic_region'`.  The axiom `Nivat.colle_region` that used to stand in for this
theorem in `Section8/External.lean` is deleted.  Measured closure of `Nivat.nivat_conjecture`
from 2026-09-18 until 2026-09-30: `[propext, sorryAx, Classical.choice, Quot.sound]`, the
`sorryAx` being exactly the open leaves of this file; since 2026-09-30 it is
`[propext, Classical.choice, Quot.sound]` — `bash scripts/sorries.sh` is the authoritative list.

So: closing the leaves here is the whole of what remains for `Nivat.nivat_conjecture` to reach
a closure of `[propext, Classical.choice, Quot.sound]`.  The line-number table above is a
snapshot from the day of extraction; it is not maintained by hand, and `sorries.sh` supersedes
it.

For two days (2026-09-16 → 18) this was not so: `region_case1`'s first clause had been weakened
to the Claim 3.7 form (a fully periodic accumulation point along `vl`), and `colle_region`'s
with it, while the axiom exported `¬ IsPeriodic ξ'`, so FROZEN E1's `rfl` substitution check
was red and no amount of leaf-closing would have retired the axiom.  Both clauses were restored
to `¬ IsPeriodic` on 2026-09-18: Case 1 from the translate (`b3_colle2.txt:846`, see the
deletion note at the old L4 site below), Case 2 from Claim 4.14 (`Claim414Wire.lean`).
`RegionClassification.lean`'s `chainData_yields_region` is **not** on this path —
`ColleRegion.lean`'s `import` lines (`:6-10`) do not include it.
-/

namespace Nivat.ColleReg

open Nivat Nivat.Colle35

variable {ξ xper ϑ : Config ℤ} {vl p ℓ : ℤ × ℤ} {S : Finset (ℤ × ℤ)} {gen : ℤ × ℤ}

/-- **The rationality step at `A := ℤ`.**  A minimal counterexample admits a *lattice*
direction `ℓ` that is nonexpansive and one-sided nonexpansive on *both* sides.

This is not a restatement of `Nivat.Colle45.claim46`: that one is itself `sorry`, *and* its
ambient `variable` block demands `[Fintype A]`, which `A := ℤ` does not satisfy, so it could
not be applied here even once proved.  The `ℤ`-valued version has to be proved separately.

## Correction, 2026-09-14: this was labelled "all of Collé §4", and that is wrong

Both this docstring and blueprint node `lem:biONED` used to call this theorem *"Claim 4.6 at
`A := ℤ`"* and *"the hardest of the six --- it is the content of all of Collé §4"*.  Checked
against the source (`scratch/b3_colle2.txt`), that is a misreading on two counts:

* Claim 4.6 (line 780) says *"`(T^u η)|R_{ι-1}` is periodic with period parallel to `ℓ`"*.
  That is a statement about a region `R_{ι-1}`, and it is **not** what this theorem asserts.
* Where §4 actually gets its bi-nonexpansive line, it *assumes* one: line 742, *"we just need
  to apply the main lemma successively, starting from a line `ℓ ∈ NEXPL(η)` such that
  `−ℓ, ℓ ∈ NEXPD(η)` ... for a not fully periodic configuration with a non-trivial annihilator
  such a line always exists (see Theorem 1.14)"*, and line 938, *"Due to Lemma 2.6, we know
  that `ℓ` contains some vector `h_i`."*

So the content of this theorem is **Collé Lemma 2.6, the rationality step**, and nothing more.
The hypotheses already hand over a real direction `w` with `w, -w ∈ ONED ξ`; what is left is
to show that `w` may be taken *rational*, and then to read off a primitive `ℓ`.

## The proof path, with every input measured kernel-clean 2026-09-14

None of these carries `sorryAx`; all four report `[propext, Classical.choice, Quot.sound]`.

1. `hξ.1` gives `(Set.range ξ).Finite` and `LowConvexComplexity ξ`; the latter unfolds to an
   `S` with `P ξ S ≤ S.card`, so `Nivat.hasNonzeroAnn_of_low_complexity` gives
   `HasNonzeroAnn ξ`.
2. `Nivat.kari_szabados_prodShift` turns that into `h : Fin n → ℤ × ℤ`, non-zero and pairwise
   transverse, with `act (prodShift h) ξ = 0`.  `Nivat.prodShift` is by definition
   `∏ i, (mono (h i) - 1)`, which is the shape the next step wants.
3. `Nivat.Colle.exists_tangent_of_orbit_halfPlane_ambiguity` (`DirectionRigidity.lean`) is
   **already the rationality step of Lemma 2.6**.  Feed it the witnesses `x ≠ y` of
   `hw₁ : w ∈ ONED ξ` at `w := -w`, `c := 0` --- legitimate because
   `inner2 (-w) z = -inner2 w z`, so `0 ≤ inner2 (-w) z ↔ z ∈ sideOf w`.  Out comes
   `∃ i, inner2 w (h i) = 0`: the direction is orthogonal to a lattice vector, i.e. rational.
4. Elementary lattice geometry, the only genuinely new work.  With `v := h i ≠ 0` and
   `inner2 w v = 0`, `w` is a non-zero real multiple `t` of `toReal (-v.2, v.1)`; by
   `Nivat.LE2.inner2_toReal`, `inner2 w z = t * (dot (-v.2, v.1) z : ℝ)`.  Take
   `m := (-v.2, v.1)` if `t > 0` and `m := (v.2, -v.1)` if `t < 0`, so that
   `sideOf w = {z | dot m z ≤ 0}` on the nose; then `Nivat.exists_primitive_nsmul_eq`
   (`Nivat/Lattice/Primitive.lean`, public) writes `m = k • ℓ` with `ℓ` primitive and `k > 0`,
   and `dot m z = k * dot ℓ z` has the same sign.

`sideOf (-w) = {z | dot (-ℓ) z ≤ 0}` by the same computation, so `hw₂` discharges the third
conjunct.  The three conclusions then differ from `hw₁`/`hw₂` only by unfolding
`Colle45.IsOneSidedNonexpansive` and `halfPlaneLE`, plus `Primitive ℓ` from step 4.

The obstacle recorded in `Lemma45.lean` --- that `ℓ` and `-ℓ` cannot be one-sided nonexpansive
*with the same witness pair*, since the two half-planes cover the plane and meet only on the
line --- is not in the way here: `hw₁` and `hw₂` are separate memberships of `ONED ξ`, so they
supply two independent witness pairs, which is exactly what that warning says is needed.

`hξ` is used only through `IsCounterexample`; minimality is not needed.

## Closed 2026-09-14 --- `Step_BiONED.lean`

Proved along exactly the path above.  This declaration is now an alias, and the
substitution was checked mechanically rather than by eye:
`example : @Nivat.ColleReg.exists_biONED_direction = @Nivat.ColleStep.exists_biONED_direction
:= rfl` elaborates (with a negative control at `exists_chainData` that fails), so the two
types are defeq and no hypothesis was added.  Measured closure of the proof:
`[propext, Classical.choice, Quot.sound]` --- no `sorryAx`. -/
theorem exists_biONED_direction (hξ : IsMinimalCounterexample ξ)
    {w : ℝ × ℝ} (hw : w ≠ 0) (hw₁ : w ∈ ONED ξ) (hw₂ : -w ∈ ONED ξ) :
    ∃ ℓ : ℤ × ℤ, ℓ ∈ Colle45.NonExpansiveLine ξ ∧
      Colle45.IsOneSidedNonexpansive ξ ℓ ∧
      Colle45.IsOneSidedNonexpansive ξ (-ℓ) :=
  Nivat.ColleStep.exists_biONED_direction hξ hw hw₁ hw₂

/-! ## The case split of Lemma 4.5

`Case1` / `Case2` and their two exhaustiveness lemmas (`not_case2_of_case1`,
`case1_of_not_case2`) moved **verbatim** to `Nivat/External/Colle/CaseSplit.lean` on
2026-09-19, keeping namespace `Nivat.ColleReg` and every full name.  They are re-exported
by the `import` above, so references here and in `ColleRegion.lean` / `DecompData.lean` /
`L1Data.lean` / `ONEDRational.lean` are unchanged.

The move is not cosmetic: `StepHypSeam.stepHyp_of_case2` (`StepHypSeam.lean:59`) is a
producer for `exists_chainData` below, and while `Case2` was defined *in this file* that
producer was pinned downstream of the `sorry` it feeds.  See `CaseSplit.lean` for the
full rationale and for the text that used to stand here. -/

/-- **Why joint 1 reads `dot`, not `det`** (2026-09-17).  If `n ≠ 0` is a normal and `u ≠ 0`
lies on its line, `dot n u = 0`, then `u` is *not* parallel to `n`.  Proposition 2.10
(`Nivat.Colle.colle_prop_2_10`) returns a period `u` with `inner2 w u = 0`, i.e. `dot ℓ u = 0`
for the Lean `ℓ` (a normal, `Lemma45.lean:97`); so the former conjunct `det ℓ vl = 0` of
`exists_preamble` could never have been produced along the route of Collé.  Kept as the
compiled record of the correction, in the spirit of `ColleRegion.old_guard_forces_eq`. -/
theorem det_ne_zero_of_dot_eq_zero {n u : ℤ × ℤ} (hn : n ≠ 0) (hu : u ≠ 0)
    (h : Nivat.LE2.dot n u = 0) : det n u ≠ 0 := by
  intro hd
  simp only [Nivat.LE2.dot] at h
  simp only [det] at hd
  have h1 : (n.1 ^ 2 + n.2 ^ 2) * u.1 = 0 := by linear_combination n.1 * h - n.2 * hd
  have h2 : (n.1 ^ 2 + n.2 ^ 2) * u.2 = 0 := by linear_combination n.2 * h + n.1 * hd
  have hn2 : n.1 ^ 2 + n.2 ^ 2 ≠ 0 := by
    intro h0
    apply hn
    have ha : n.1 = 0 := by nlinarith [sq_nonneg n.1, sq_nonneg n.2]
    have hb : n.2 = 0 := by nlinarith [sq_nonneg n.1, sq_nonneg n.2]
    exact Prod.ext ha hb
  exact hu (Prod.ext ((mul_eq_zero.mp h1).resolve_left hn2)
    ((mul_eq_zero.mp h2).resolve_left hn2))

/-- **Bridge from the exported Lemma 2.4 deficit to the `hdef` of Lemma 4.1** (2026-09-17).

`exists_preamble` exports the bound of `Nivat.R2.exists_generatingSet_biOriented` in the
shape `P ξ S - P ξ Q ≤ (face S n c).card - 1` (natural-number subtraction), universally
quantified over the normal `n` and the two levels, with four premises.  Lemma 4.1
(`Nivat.Colle41.lemma41_of_sweep`, `Lemma41.lean:706`, and
`wordsFrom_ncard_le_of_semiAmbiguous`, `:550`) wants `hdef : P η S ≤ P η Q + p`.  This lemma
does the conversion at the `n`-minimal face for any normal `n` the consumer picks: the four
premises are discharged by `Finset.exists_min_image` / `exists_max_image` over the nonempty
`S`, and the arithmetic is `Nat.sub_le_iff_le_add : a - b ≤ c ↔ a ≤ c + b` — note the
summand order `c + b` in Mathlib v4.33.1, which is the reverse of the `Q + p` wanted here;
`omega` closes the gap.  `Q` and `p` are returned as equations rather than substituted, so the
consumer can `subst` or keep them abstract. -/
theorem deficit_to_lemma41_shape {ξ : Config ℤ} {S : Finset (ℤ × ℤ)} (hSne : S.Nonempty)
    (n : ℝ × ℝ)
    (hdef : ∀ (n : ℝ × ℝ) (cmax cmin : ℝ),
      (∀ z ∈ S, inner2 n z ≤ cmax) → (Nivat.R2.face S n cmax).Nonempty →
      (∀ z ∈ S, cmin ≤ inner2 n z) → (Nivat.R2.face S n cmin).Nonempty →
        P ξ S - P ξ (S.filter fun z => inner2 n z < cmax) ≤
          (Nivat.R2.face S n cmax).card - 1 ∧
        P ξ S - P ξ (S.filter fun z => cmin < inner2 n z) ≤
          (Nivat.R2.face S n cmin).card - 1) :
    ∃ (c : ℝ) (Q : Finset (ℤ × ℤ)) (p : ℕ), Q ⊆ S ∧ (∀ z ∈ S, c ≤ inner2 n z) ∧
      Q = S.filter (fun z => c < inner2 n z) ∧ p = (Nivat.R2.face S n c).card - 1 ∧
      P ξ S ≤ P ξ Q + p := by
  classical
  obtain ⟨zmin, hzminS, hzmin⟩ := S.exists_min_image (fun z => inner2 n z) hSne
  obtain ⟨zmax, hzmaxS, hzmax⟩ := S.exists_max_image (fun z => inner2 n z) hSne
  have h := (hdef n (inner2 n zmax) (inner2 n zmin) hzmax
    ⟨zmax, Finset.mem_filter.mpr ⟨hzmaxS, rfl⟩⟩ hzmin
    ⟨zmin, Finset.mem_filter.mpr ⟨hzminS, rfl⟩⟩).2
  refine ⟨inner2 n zmin, _, _, Finset.filter_subset _ _, hzmin, rfl, rfl, ?_⟩
  have h2 := Nat.sub_le_iff_le_add.mp h
  omega

/-- **The preamble of Lemma 4.5** (`b3_colle2.txt:774-776`), verbatim:

> Let `𝒮 ⊂ ℤ²`, with `𝒮 ∩ ℓ_𝒮` contained in `ℓ^(−)`, be an `η`-generating set as in
> **Lemma 2.4**, which according to **Lemma 2.3** has an edge parallel to `ℓ` and another one
> parallel to `−ℓ`. … Since `ℓ ∈ nexpd(η)`, then there exist configurations
> `x_per, y_per ∈ X_η` such that `x_per|ℋ(ℓ) = y_per|ℋ(ℓ)`, but `(x_per)_g ≠ (y_per)_g` for
> some `g ∈ ℓ^(−) ∩ ℤ²`. … Thus, **Propositions 2.10 and 2.12** imply that `x_per` and
> `y_per` are periodic with periods parallels to `ℓ`.

Only the part both branches consume is stated: the generating set `S`, the configuration
`x_per ∈ X_η` with a non-zero period `p` parallel to the line `ℓ` (`det p vl = 0` together
with `dot ℓ vl = 0`; recall that the Lean `ℓ` is the *normal*, joint 1), and the direction
`vl = v_ℓ`.  The witness `y_per` is deliberately not exported; no branch currently uses it.

Also exported (2026-09-17, second pass): the **Lemma 2.4 complexity-deficit bound** at both
supporting faces of *every* real normal `n`, in the exact spelling of
`Nivat.R2.exists_generatingSet_biOriented` — the conjunct is the third output of that
theorem, and `S` is the set it returns, so the bound costs nothing here.  It is exported for
every normal rather than for the two faces of `ℓ` alone because (a) the orientation actually
used inside the proof is deliberately not exported (next section), so a single `ℓ`-face bound
would name a face the argument may not have used, and (b) Lemma 4.1 (`Lemma41.lean:706`,
`hdef : P η S ≤ P η Q + p`) is applied downstream at a normal that need not be `ℓ`
(Claim 4.11 runs along `ℓ_J`).  The consumer picks `n`, `Q := S.filter (c < inner2 n ·)`,
`p := (face S n c).card - 1` and converts with `Nat.sub_le_iff_le_add`; the four premises are
discharged by `Finset.exists_min_image` / `exists_max_image` on `inner2 n` over the nonempty
`S`.

## The `|𝒮 ∩ ℓ_𝒮| ≤ |𝒮 ∩ −ℓ_𝒮|` normalisation is free here, and this is not obvious

`b3_colle2.txt:774` says *"We will suppose **initially** that `|𝒮 ∩ ℓ_𝒮| ≤ |𝒮 ∩ −ℓ_𝒮|`"*.
The hypothesis is not decorative: it is carried by **Proposition 2.10** itself
(`b3_colle2.txt:359`, Cyr–Kra), which is what makes `x_per` periodic, and
`R2Orientation.lean` records at length that at complexity `P_η(S) ≤ |S|` it cannot be arranged
for a *prescribed* orientation (`neg_notMem_ONED_of_lower_face_card_le_one` shows the failure
is not a write-up artefact).

Collé discharges it at the very end of Lemma 4.5, **after both cases**, at
`b3_colle2.txt:936`: *"The case `|𝒮 ∩ −ℓ_𝒮| < |𝒮 ∩ ℓ_𝒮|` follows from the previous one by
considering the enumeration `ℓ̂₁,…,ℓ̂_{2m}` where `ℓ̂_ι = −ℓ_ι`"*.  Note that this sentence
contains no WLOG keyword — it is invisible to a grep for "suppose initially" or "In the case
that", and the hit those patterns *do* produce, `b3_colle2.txt:702`, belongs to a different
WLOG (opened at `:627`, inside **Lemma 4.3**).

The mechanism is reversal of the whole edge enumeration, not a local swap of `ℓ`: `ℓ̂_ι = −ℓ_ι`
for every `ι`, which is legitimate because Lemma 4.5's hypothesis (`−ℓ_ι, ℓ_ι ∈ nexpd(η)`) and
its conclusion are both symmetric under it.  For *this* theorem the same reversal is available
locally and costs nothing: `ℓ` and `−ℓ` are both in hand (`hℓ_pos`, `hℓ_neg`), the inequality
holds for at least one of the two orientations, and every conjunct of the conclusion is
invariant under `ℓ ↦ −ℓ` — `dot ℓ vl = 0` because `dot (−ℓ) vl = −dot ℓ vl`, and `p ∈ Per xper`
because `b3_colle2.txt:361` says *"a configuration is periodic with period parallel to `ℓ` if
and only if it is periodic with period parallel to `−ℓ`"*.

So: whoever proves this may pick the orientation, and **must not** export the inequality —
doing so would push the `R2Orientation.lean` gap into the callers, where it is not free.
⚠ If the conclusion ever gains a conjunct that is *not* `ℓ ↦ −ℓ`-symmetric, this reasoning
lapses and the orientation must be threaded through explicitly.  (The deficit conjunct added
on 2026-09-17 does not mention `ℓ` at all, so it is symmetric trivially.  The partner conjunct
added on 2026-09-18 does not mention `ℓ` either: the orientation it needs is carried by an
existentially bound **vector** `nℓ`, constrained only by `nℓ ≠ 0` and `dot nℓ vl = 0`, and
instantiated at `ℓ` in one branch and at `−ℓ` in the other.  Exporting instead an inequality
relating the agreement half plane to `ℓ` would be exactly the mistake this paragraph forbids.)

### 2026-09-24 (集成者): the ⚠ above has now fired, and is discharged by normalisation

The conclusion gained the conjunct `0 < det nℓ vl`, which is **not** `ℓ ↦ −ℓ`-symmetric — it is
the one datum the interface used to drop.  Per the ⚠, the orientation is therefore threaded
explicitly, and the threading is done *here, at the producer*, not pushed to the callers:

* the `by_cases hle` picks only the partner normal `nℓ` (`ℓ` / `−ℓ`) while `v₀ = dir ℓ` is
  branch-independent, so the old export carried `0 < det nℓ vl` in one branch and
  `det nℓ vl < 0` in the other;
* the `¬hle` branch now exports `−v₀ = dir (−ℓ)` instead of `v₀`, so in **both** branches
  `vl = dir nℓ` and `det nℓ vl = ‖nℓ‖² > 0` by one computation.

This costs the callers nothing: every other `vl`-mentioning conjunct is `vl ↦ −vl` invariant,
which is `Nivat.ColleOrient.preamble_output_vl_neg` (`OrientationFree.lean`), compiled.  That
file also records *why* the bit had to be pinned here rather than derived downstream: it is not
a function of `ξ` (`preamble_input_symm`) and not recoverable from the exported data
(`det_nl_vl_sign_free`).

⚠ **Corrected 2026-09-24, same day.**  The first version of this paragraph named
`Hole3Room.nlmax_of_wadj`'s `hmvl` (`Hole3Room.lean:321`) as the consumer.  **Wrong:** that
`hmvl` is `0 < dot m vl` for the *cut* normal `m` (`dot m w = 0`), a different vector from `nℓ`
(`dot nℓ vl = 0`), and the tower package already discharges it — `hmvl` in the `obtain` at
`:1949`.  What this conjunct
actually buys, downstream:
* `dir vl = −nℓ` — the normal/tangent dictionary is pinned on-chain, not merely up to sign
  (`LaneTowerPkgRegion.dir_vl_eq_neg_nl`);
* `0 < det vl w`, via the prefix-free identity
  `det nℓ vl * det vl w + dot nℓ w * ‖vl‖² = dot nℓ vl * dot vl w` together with `hperp` and
  the tower package's `dot nℓ w < 0` (`hwneg`, in the `obtain` at `:1949`) — i.e. `LE2.IsRegion`'s `detPos`
  (`LatticeEdges.lean:2300`) in the orientation `(vl, w)`;
* `det u' vl = −1`, killing the other disjunct of `hunimod` (this theorem's binder, `:1904`)
  on-chain: `hperp` plus
  `Primitive vl` force `nℓ = k • dir vl`, then `hnu` (binder, `:1920`) gives `k * det u' vl = 1` and
  this conjunct gives `k = −1`.  No vacuity — the caller picks `u'` after `nℓ`.

⚠ The chain's `0 < det vl w` is **our** convention, not the paper's.  lane-towerpkg's rig reads
the paper side as `det vl w = −1 < 0`.  Until "chain `vl` = paper `v⃗_{ℓ_ι}`" is proved, do not
import signed paper-side facts about `det vl w` into the chain.

⚠ The paragraph above still governs the *inequality* `|S ∩ ℓ_S| ≤ |S ∩ −ℓ_S|`: that is still
not exported, and must not be.  What is exported is a determinant sign that the producer can
always arrange, which is a different thing.

The conjuncts are the ones `exists_chainData` used to bind existentially before
2026-09-17, so the two call sites are unchanged apart from the hoisting — and apart from
the last conjunct, corrected from `det ℓ vl = 0` to `dot ℓ vl = 0` the same day (joint 1).

## Closed 2026-09-17

Every input below was measured kernel-clean before use; the route follows the source
sentence by sentence, with the Lean `ℓ` a normal throughout (joint 1).

1. `w₀ := (ℓ.1, ℓ.2) : ℝ × ℝ`, so `inner2 w₀ z = dot ℓ z`, and `v₀ := (-ℓ.2, ℓ.1)`, primitive
   with `dot ℓ v₀ = 0` — this is the exported `vl`.  `hℓ_neg` / `hℓ_pos` unfold to the `honed`
   hypothesis of `Nivat.Colle.colle_prop_2_10` at `w₀` / at `-w₀`.
2. **Lemma 2.4**: `Nivat.R2.exists_generatingSet_biOriented` gives `S` with
   `IsGeneratingSet ξ S` and the complexity-deficit bound at *both* extreme faces of every
   normal, which is the `hcount` of `colle_prop_2_10` in either orientation and is passed
   through unchanged as the last conjunct.  `hmin`/`hmax`/`hfc` are
   `Finset.exists_min_image` / `exists_max_image` on `inner2 w₀`.
3. `b3_colle2.txt:355`: `Nivat.Colle.exists_ambiguousAlong_of_oneSidedNonexpansive`
   (`Prop210.lean`) produces the `(ℓ,𝒮)`-ambiguous `x_per ∈ X_η` — no compactness needed.
4. **Proposition 2.10** (`colle_prop_2_10`) gives `u ≠ 0`, `inner2 w' u = 0`, a period of
   `x_per` on the lower half plane; **Proposition 2.12**
   (`Nivat.Colle.period_multiple_of_periodicDecompZ`) turns a multiple `k • u` into a period
   of `x_per` everywhere.  The `PeriodicDecompZ x_per n` it needs is `hξ` itself through
   `IsMinimalCounterexample.of_mem_orbitClosure` (`n = 1` if `x_per` is already periodic).
5. `gen` is the `dotZ`-minimal endpoint of the lower face, generated by
   `Nivat.Colle.generatesAt_of_min_on_face`; `det p vl = 0` is
   `Nivat.Colle.det_eq_zero_of_inner2_eq_zero`.

The orientation is chosen inside the proof exactly as the section above prescribes: the
core runs at `w₀` when `|S ∩ ℓ_S| ≤ |S ∩ −ℓ_S|` and at `-w₀` otherwise
(`Nivat.R2.face_neg_level` transports the faces), and the inequality is not exported.  The
translation normalisation `𝒮 ∩ ℓ_𝒮 ⊂ ℓ^(−)` of `b3_colle2.txt:774` turned out not to be
needed: `colle_prop_2_10` is stated with the face level `c` free, so nothing depends on
where `S` sits.  The `hSgen` conjunct is the output of Lemma 2.4 itself; `hgen` is step 5. -/
theorem exists_preamble (hξ : IsMinimalCounterexample ξ)
    {w : ℝ × ℝ} (hw : w ≠ 0) (hw₁ : w ∈ ONED ξ) (hw₂ : -w ∈ ONED ξ)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_pos : Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ)) :
    ∃ (xper : Config ℤ) (vl p : ℤ × ℤ) (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ),
      xper ∈ orbitClosure ξ ∧ Nivat.Colle.GeneratesAt ξ S gen ∧
      Nivat.Colle.IsGeneratingSet ξ S ∧
      p ∈ Per xper ∧ p ≠ 0 ∧ vl ≠ 0 ∧ Primitive vl ∧ det p vl = 0 ∧
      Nivat.LE2.dot ℓ vl = 0 ∧
      -- the ambiguity partner `y_per` of `b3_colle2.txt:774`, with the orientation carried by
      -- a *vector* `nℓ` rather than by an inequality about `S`; see "Orientation" above
      (∃ (yper : Config ℤ) (nℓ : ℤ × ℤ) (cz : ℤ), yper ∈ orbitClosure ξ ∧ xper ≠ yper ∧
        nℓ ≠ 0 ∧ Nivat.LE2.dot nℓ vl = 0 ∧ 0 < det nℓ vl ∧
        ∀ z : ℤ × ℤ, cz ≤ Nivat.LE2.dot nℓ z → xper z = yper z) ∧
      ∀ (n : ℝ × ℝ) (cmax cmin : ℝ),
        (∀ z ∈ S, inner2 n z ≤ cmax) → (Nivat.R2.face S n cmax).Nonempty →
        (∀ z ∈ S, cmin ≤ inner2 n z) → (Nivat.R2.face S n cmin).Nonempty →
          P ξ S - P ξ (S.filter fun z => inner2 n z < cmax) ≤
            (Nivat.R2.face S n cmax).card - 1 ∧
          P ξ S - P ξ (S.filter fun z => cmin < inner2 n z) ≤
            (Nivat.R2.face S n cmin).card - 1 := by
  classical
  have hfin : (Set.range ξ).Finite := hξ.1.1
  have hlow : LowConvexComplexity ξ := hξ.1.2.2.2
  obtain ⟨hℓprim, -⟩ := hℓ_nel
  have hℓ0 : ℓ ≠ 0 := hℓprim.ne_zero
  -- ### the real normal `w₀ = ℓ` and the primitive tangent `v₀`
  set w₀ : ℝ × ℝ := ((ℓ.1 : ℝ), (ℓ.2 : ℝ)) with hw₀
  have hw₀form : ∀ z : ℤ × ℤ, inner2 w₀ z = ((Nivat.LE2.dot ℓ z : ℤ) : ℝ) := by
    intro z; simp only [inner2, Nivat.LE2.dot, hw₀]; push_cast; ring
  have hw₀ne : w₀ ≠ 0 := by
    intro h
    rw [hw₀, Prod.mk_eq_zero] at h
    obtain ⟨h1, h2⟩ := h
    exact hℓ0 (Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2))
  set v₀ : ℤ × ℤ := (-ℓ.2, ℓ.1) with hv₀
  have hv₀prim : Primitive v₀ := by
    obtain ⟨a, b, hab⟩ := hℓprim
    exact ⟨-b, a, by simp only [hv₀]; linear_combination hab⟩
  have hv₀ne : v₀ ≠ 0 := hv₀prim.ne_zero
  have hw₀v₀ : inner2 w₀ v₀ = 0 := by
    simp only [inner2, hw₀, hv₀]; push_cast; ring
  have hdotv₀ : Nivat.LE2.dot ℓ v₀ = 0 := by simp only [Nivat.LE2.dot, hv₀]; ring
  -- ### orientation normalisation (集成者 2026-09-24): export `dir nℓ`, never plain `dir ℓ`
  -- The `by_cases hle` below picks only the *partner normal* `nℓ` (`ℓ` in one branch, `-ℓ` in
  -- the other) while `v₀ = dir ℓ` is branch-independent, so a naive export would carry
  -- `0 < det nℓ vl` in one branch and `det nℓ vl < 0` in the other.  `Nivat.ColleOrient`
  -- (`OrientationFree.lean`) proves that bit is not a function of `ξ` and is not recoverable
  -- from the exported interface, so it is pinned *here*, at the producer: the `¬hle` branch
  -- exports `-v₀ = dir (-ℓ)` in place of `v₀`, and then both branches satisfy
  -- `det nℓ vl = ‖nℓ‖² > 0` by the same computation.  Every `vl`-mentioning conjunct of the
  -- conclusion is `vl ↦ -vl` invariant (`ColleOrient.preamble_output_vl_neg`), so the swap is
  -- free.  What the new conjunct buys downstream is `dir vl = -nℓ`, `0 < det vl w`, and
  -- `det u' vl = -1`; see the "orientation normalisation" section of `exists_preamble`'s
  -- docstring above, including the ⚠ that the first version of that paragraph named the wrong
  -- consumer (`Hole3Room.nlmax_of_wadj`'s `hmvl` is about the *cut* normal `m`, already
  -- discharged by the tower package at `hmvl`（本文件 `:1949` 的 `obtain`）).
  have hℓcoord : ℓ.1 ≠ 0 ∨ ℓ.2 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hℓ0 (Prod.ext hc.1 hc.2)
  have hdetv₀ : det ℓ v₀ = ℓ.1 * ℓ.1 + ℓ.2 * ℓ.2 := by simp only [det, hv₀]; ring
  have hdetpos : 0 < det ℓ v₀ := by
    rw [hdetv₀]
    rcases hℓcoord with h1 | h2
    · nlinarith [mul_self_nonneg ℓ.2, mul_self_pos.mpr h1]
    · nlinarith [mul_self_nonneg ℓ.1, mul_self_pos.mpr h2]
  have hnv₀ne : (-v₀) ≠ 0 := neg_ne_zero.mpr hv₀ne
  have hnv₀prim : Primitive (-v₀) := by
    obtain ⟨a, b, hab⟩ := hv₀prim
    exact ⟨-a, -b, by simp only [Prod.fst_neg, Prod.snd_neg]; linear_combination hab⟩
  have hdotnv₀ : Nivat.LE2.dot ℓ (-v₀) = 0 := by
    simp only [Nivat.LE2.dot, Prod.fst_neg, Prod.snd_neg] at hdotv₀ ⊢
    linear_combination -hdotv₀
  have hdotnegnv₀ : Nivat.LE2.dot (-ℓ) (-v₀) = 0 := by
    simp only [Nivat.LE2.dot, Prod.fst_neg, Prod.snd_neg] at hdotv₀ ⊢
    linear_combination hdotv₀
  have hdetposneg : 0 < det (-ℓ) (-v₀) := by
    have h : det (-ℓ) (-v₀) = det ℓ v₀ := by
      simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
    rw [h]; exact hdetpos
  -- ### `ℓ ∈ nexpd(η)` in the two orientations, as `colle_prop_2_10` wants it
  have honed₀ : ∃ y ∈ orbitClosure ξ, ∃ y' ∈ orbitClosure ξ, y ≠ y' ∧
      ∀ z : ℤ × ℤ, 0 ≤ inner2 w₀ z → y z = y' z := by
    obtain ⟨x, y, hx, hy, hne, hagr⟩ := hℓ_neg
    refine ⟨x, hx, y, hy, hne, fun z hz => hagr z ?_⟩
    rw [Nivat.LE2.dot_neg_left]
    rw [hw₀form] at hz
    have : (0 : ℤ) ≤ Nivat.LE2.dot ℓ z := by exact_mod_cast hz
    linarith
  have honed₁ : ∃ y ∈ orbitClosure ξ, ∃ y' ∈ orbitClosure ξ, y ≠ y' ∧
      ∀ z : ℤ × ℤ, 0 ≤ inner2 (-w₀) z → y z = y' z := by
    obtain ⟨x, y, hx, hy, hne, hagr⟩ := hℓ_pos
    refine ⟨x, hx, y, hy, hne, fun z hz => hagr z ?_⟩
    rw [Nivat.R2.inner2_neg_left, hw₀form] at hz
    have : ((Nivat.LE2.dot ℓ z : ℤ) : ℝ) ≤ 0 := by linarith
    exact_mod_cast this
  -- ### Lemma 2.4: the generating set, with the deficit bound at both faces
  obtain ⟨S, hSgen, -, hdef⟩ := Nivat.R2.exists_generatingSet_biOriented hfin hlow
  have hSne : S.Nonempty := hSgen.1
  obtain ⟨zmin, hzminS, hzmin⟩ := S.exists_min_image (fun z => inner2 w₀ z) hSne
  obtain ⟨zmax, hzmaxS, hzmax⟩ := S.exists_max_image (fun z => inner2 w₀ z) hSne
  set cmin : ℝ := inner2 w₀ zmin with hcmin
  set cmax : ℝ := inner2 w₀ zmax with hcmax
  have hmin : ∀ z ∈ S, cmin ≤ inner2 w₀ z := hzmin
  have hmax : ∀ z ∈ S, inner2 w₀ z ≤ cmax := hzmax
  have hfmin : (S.filter fun z => inner2 w₀ z = cmin).Nonempty :=
    ⟨zmin, Finset.mem_filter.mpr ⟨hzminS, rfl⟩⟩
  have hfmax : (S.filter fun z => inner2 w₀ z = cmax).Nonempty :=
    ⟨zmax, Finset.mem_filter.mpr ⟨hzmaxS, rfl⟩⟩
  obtain ⟨hcount_max, hcount_min⟩ := hdef w₀ cmax cmin hmax hfmax hmin hfmin
  -- ### the orientation-free core: 2.10 → 2.12 → a period tangent to `w'`
  have core : ∀ (w' : ℝ × ℝ) (c c' : ℝ), w' ≠ 0 → inner2 w' v₀ = 0 →
      (∀ z ∈ S, c ≤ inner2 w' z) → (∀ z ∈ S, inner2 w' z ≤ c') →
      (S.filter fun z => inner2 w' z = c).Nonempty →
      (S.filter fun z => inner2 w' z = c).card ≤ (S.filter fun z => inner2 w' z = c').card →
      P ξ S - P ξ (S.filter fun z => c < inner2 w' z) ≤
        (S.filter fun z => inner2 w' z = c).card - 1 →
      (∃ y ∈ orbitClosure ξ, ∃ y' ∈ orbitClosure ξ, y ≠ y' ∧
        ∀ z : ℤ × ℤ, 0 ≤ inner2 w' z → y z = y' z) →
      ∃ (xper : Config ℤ) (p : ℤ × ℤ) (gen : ℤ × ℤ), xper ∈ orbitClosure ξ ∧
        Nivat.Colle.GeneratesAt ξ S gen ∧ p ∈ Per xper ∧ p ≠ 0 ∧ det p v₀ = 0 ∧
        ∃ yper ∈ orbitClosure ξ, xper ≠ yper ∧
          ∃ c'' : ℝ, ∀ z : ℤ × ℤ, c'' ≤ inner2 w' z → xper z = yper z := by
    intro w' c c' hw' hw'v hmin' hmax' hfc' hle' hcount' honed'
    -- `b3_colle2.txt:355`: an ambiguous `x_per ∈ X_η`, with its partner `y_per`
    obtain ⟨x, hx, hamb, hpair⟩ := Nivat.Colle.exists_ambiguousAlong_of_oneSidedNonexpansive
      hSgen hv₀prim hw' hw'v hmin' hfc' honed'
    -- Proposition 2.10: the lower half plane of `x_per` has a period `u` tangent to `w'`
    obtain ⟨u, hu0, huw, huper⟩ := Nivat.Colle.colle_prop_2_10 hfin hx hSgen hv₀prim hw' hw'v
      hmin' hmax' hfc' hle' hcount' honed' hamb
    -- a generated vertex: the `dotZ`-minimal endpoint of the lower face
    obtain ⟨a, haF, hamin⟩ :=
      (S.filter fun z => inner2 w' z = c).exists_min_image (fun z => Nivat.Colle.dotZ z v₀) hfc'
    obtain ⟨haS, hac⟩ := Finset.mem_filter.mp haF
    have hgenA : Nivat.Colle.GeneratesAt ξ S a :=
      Nivat.Colle.generatesAt_of_min_on_face hSgen hv₀prim hw' hw'v hmin' haS hac
        (fun z hz hzc => hamin z (Finset.mem_filter.mpr ⟨hz, hzc⟩))
    -- `x_per` has a finite periodic decomposition (Remark 8.3 / Lemma 8.5(a))
    obtain ⟨n, hdec⟩ : ∃ n, PeriodicDecompZ x n := by
      by_cases hper : IsPeriodic x
      · exact ⟨1, fun _ => x, fun _ => hper, fun z => by simp⟩
      · obtain ⟨n, hord, -⟩ := hξ.2
        exact ⟨n, ((hξ.of_mem_orbitClosure hx hper).2 n hord).1⟩
    -- Proposition 2.12, on the half plane `{inner2 w' · ≤ c} = {-c ≤ inner2 (-w') ·}`
    have hw'ne : -w' ≠ 0 := neg_ne_zero.mpr hw'
    have huw' : inner2 (-w') u = 0 := by rw [Nivat.R2.inner2_neg_left, huw, neg_zero]
    have hlocal : ∀ z, -c ≤ inner2 (-w') z → x (z + u) = x z := by
      intro z hz
      apply huper
      rw [Nivat.R2.inner2_neg_left] at hz
      linarith
    obtain ⟨k, hk, hkper⟩ :=
      Nivat.Colle.period_multiple_of_periodicDecompZ hdec hw'ne hu0 huw' hlocal
    refine ⟨x, k • u, a, hx, hgenA, hkper, zsmul_ne_zero_of_ne_zero hk hu0, ?_, hpair⟩
    have hkw : inner2 w' (k • u) = 0 := by rw [inner2_zsmul, huw, mul_zero]
    exact Nivat.Colle.det_eq_zero_of_inner2_eq_zero hw' hkw hw'v
  -- ### pick the orientation with `|S ∩ l_S| ≤ |S ∩ -l_S|` (`b3_colle2.txt:774`, `:936`)
  -- the agreement level of the partner is real; `⌈·⌉` puts it back on the lattice
  have hceil : ∀ (m : ℤ × ℤ) (cr : ℝ) (xp yp : Config ℤ),
      (∀ z : ℤ × ℤ, cr ≤ ((Nivat.LE2.dot m z : ℤ) : ℝ) → xp z = yp z) →
      ∀ z : ℤ × ℤ, ⌈cr⌉ ≤ Nivat.LE2.dot m z → xp z = yp z := by
    intro m cr xp yp h z hz
    refine h z ?_
    have h1 : cr ≤ ((⌈cr⌉ : ℤ) : ℝ) := Int.le_ceil cr
    have h2 : ((⌈cr⌉ : ℤ) : ℝ) ≤ ((Nivat.LE2.dot m z : ℤ) : ℝ) := by exact_mod_cast hz
    linarith
  by_cases hle : (S.filter fun z => inner2 w₀ z = cmin).card ≤
      (S.filter fun z => inner2 w₀ z = cmax).card
  · obtain ⟨xper, p, gen, hx, hgenA, hp, hp0, hdet, yper, hyper, hne, cr, hcr⟩ :=
      core w₀ cmin cmax hw₀ne hw₀v₀ hmin hmax hfmin hle hcount_min honed₀
    exact ⟨xper, v₀, p, S, gen, hx, hgenA, hSgen, hp, hp0, hv₀ne, hv₀prim, hdet, hdotv₀,
      ⟨yper, ℓ, ⌈cr⌉, hyper, hne, hℓ0, hdotv₀, hdetpos,
        hceil ℓ cr xper yper fun z hz => hcr z (by rw [hw₀form]; exact hz)⟩, hdef⟩
  · push_neg at hle
    have hface_max : (S.filter fun z => inner2 (-w₀) z = -cmax)
        = S.filter fun z => inner2 w₀ z = cmax := Nivat.R2.face_neg_level S w₀ cmax
    have hface_min : (S.filter fun z => inner2 (-w₀) z = -cmin)
        = S.filter fun z => inner2 w₀ z = cmin := Nivat.R2.face_neg_level S w₀ cmin
    have hmin' : ∀ z ∈ S, -cmax ≤ inner2 (-w₀) z := by
      intro z hz; rw [Nivat.R2.inner2_neg_left]; linarith [hmax z hz]
    have hmax' : ∀ z ∈ S, inner2 (-w₀) z ≤ -cmin := by
      intro z hz; rw [Nivat.R2.inner2_neg_left]; linarith [hmin z hz]
    have hfmin' : (S.filter fun z => inner2 (-w₀) z = -cmax).Nonempty := by
      rw [hface_max]; exact hfmax
    have hle' : (S.filter fun z => inner2 (-w₀) z = -cmax).card ≤
        (S.filter fun z => inner2 (-w₀) z = -cmin).card := by
      rw [hface_max, hface_min]; exact hle.le
    have hQ : (S.filter fun z => -cmax < inner2 (-w₀) z)
        = S.filter fun z => inner2 w₀ z < cmax := by
      refine Finset.filter_congr fun z _ => ?_
      rw [Nivat.R2.inner2_neg_left]
      constructor <;> intro h <;> linarith
    have hcount' : P ξ S - P ξ (S.filter fun z => -cmax < inner2 (-w₀) z) ≤
        (S.filter fun z => inner2 (-w₀) z = -cmax).card - 1 := by
      rw [hface_max, hQ]; exact hcount_max
    have hw₀v₀' : inner2 (-w₀) v₀ = 0 := by rw [Nivat.R2.inner2_neg_left, hw₀v₀, neg_zero]
    have hnegform : ∀ z : ℤ × ℤ, inner2 (-w₀) z = ((Nivat.LE2.dot (-ℓ) z : ℤ) : ℝ) := by
      intro z
      rw [Nivat.R2.inner2_neg_left, hw₀form, Nivat.LE2.dot_neg_left]
      push_cast; ring
    obtain ⟨xper, p, gen, hx, hgenA, hp, hp0, hdet, yper, hyper, hne, cr, hcr⟩ :=
      core (-w₀) (-cmax) (-cmin) (neg_ne_zero.mpr hw₀ne) hw₀v₀' hmin' hmax' hfmin' hle'
        hcount' honed₁
    -- orientation normalisation: this branch's partner normal is `-ℓ`, so the exported tangent
    -- is `-v₀ = dir (-ℓ)` rather than `v₀`; see the `have hdetpos` block above.
    have hdetn : det p (-v₀) = 0 := by
      simp only [det, Prod.fst_neg, Prod.snd_neg] at hdet ⊢
      linear_combination -hdet
    exact ⟨xper, -v₀, p, S, gen, hx, hgenA, hSgen, hp, hp0, hnv₀ne, hnv₀prim, hdetn, hdotnv₀,
      ⟨yper, -ℓ, ⌈cr⌉, hyper, hne, neg_ne_zero.mpr hℓ0, hdotnegnv₀, hdetposneg,
        hceil (-ℓ) cr xper yper fun z hz => hcr z (by rw [hnegform]; exact hz)⟩, hdef⟩

/-- **The preamble of Lemma 4.5, with the ambiguity pair put in the `b3_colle2.txt:890`
orientation** (Amink, 2026-09-19; built in `tmp/nfpL_preamble.lean`, landed here so that
`exists_chainData` can consume it).

Same conclusion as `exists_preamble` above except for the `hpartner` conjunct, which gains
three components and loses nothing a consumer was using:

* agreement weakens from `cz <= dot nl z` to the **strict** `cz < dot nl z`, and
* in exchange the level `cz` itself now carries a named **disagreement point** `g`
  (`dot nl g = cz` and `xper g != yper g`), and
* `xper` is **not doubly periodic** on the closed half plane `{z | cz <= dot nl z}`.

The third component is Colle's WLOG at `b3_colle2.txt:890`, discharged by
`Colle35.wlog_notDP` (`HalfPlaneDoublyPeriodic.lean:315`): of the two members of an
ambiguous pair, at least one fails to be doubly periodic on the half plane, and the pair may
be swapped to make it `xper`.  It is what `nfp_L` needs and what the old `hpartner` could not
state.

`exists_preamble` is kept as well: it is the weaker export, it has its own call history, and
per PROTOCOL.md `§14` a superseded statement is marked, not deleted. -/
theorem exists_preamble_pair {ξ : Config ℤ} {ℓ : ℤ × ℤ} (hξ : IsMinimalCounterexample ξ)
    {w : ℝ × ℝ} (hw : w ≠ 0) (hw₁ : w ∈ ONED ξ) (hw₂ : -w ∈ ONED ξ)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_pos : Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ)) :
    ∃ (xper : Config ℤ) (vl p : ℤ × ℤ) (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ),
      xper ∈ orbitClosure ξ ∧ Nivat.Colle.GeneratesAt ξ S gen ∧
      Nivat.Colle.IsGeneratingSet ξ S ∧
      p ∈ Per xper ∧ p ≠ 0 ∧ vl ≠ 0 ∧ Primitive vl ∧ det p vl = 0 ∧
      Nivat.LE2.dot ℓ vl = 0 ∧
      -- the ambiguity partner `y_per` of `b3_colle2.txt:774`, with the `:890` WLOG done:
      -- `cz` is the level of the line `ℓ^(−)` carrying a disagreement `g`, the pair agrees
      -- strictly above it, and `xper` is the member that is not doubly periodic on `ℋ(ℓ^(−))`
      (∃ (yper : Config ℤ) (nℓ : ℤ × ℤ) (cz : ℤ) (g : ℤ × ℤ),
        yper ∈ orbitClosure ξ ∧ xper ≠ yper ∧
        nℓ ≠ 0 ∧ Primitive nℓ ∧ Nivat.LE2.dot nℓ vl = 0 ∧ 0 < det nℓ vl ∧
        (∀ z : ℤ × ℤ, cz < Nivat.LE2.dot nℓ z → xper z = yper z) ∧
        Nivat.LE2.dot nℓ g = cz ∧ xper g ≠ yper g ∧
        ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
          PeriodicOnWith xper {z | cz ≤ Nivat.LE2.dot nℓ z} h ∧
          PeriodicOnWith xper {z | cz ≤ Nivat.LE2.dot nℓ z} h') ∧
      ∀ (n : ℝ × ℝ) (cmax cmin : ℝ),
        (∀ z ∈ S, inner2 n z ≤ cmax) → (Nivat.R2.face S n cmax).Nonempty →
        (∀ z ∈ S, cmin ≤ inner2 n z) → (Nivat.R2.face S n cmin).Nonempty →
          P ξ S - P ξ (S.filter fun z => inner2 n z < cmax) ≤
            (Nivat.R2.face S n cmax).card - 1 ∧
          P ξ S - P ξ (S.filter fun z => cmin < inner2 n z) ≤
            (Nivat.R2.face S n cmin).card - 1 := by
  classical
  have hfin : (Set.range ξ).Finite := hξ.1.1
  have hlow : LowConvexComplexity ξ := hξ.1.2.2.2
  obtain ⟨hℓprim, -⟩ := hℓ_nel
  have hℓ0 : ℓ ≠ 0 := hℓprim.ne_zero
  set w₀ : ℝ × ℝ := ((ℓ.1 : ℝ), (ℓ.2 : ℝ)) with hw₀
  have hw₀form : ∀ z : ℤ × ℤ, inner2 w₀ z = ((Nivat.LE2.dot ℓ z : ℤ) : ℝ) := by
    intro z; simp only [inner2, Nivat.LE2.dot, hw₀]; push_cast; ring
  have hw₀ne : w₀ ≠ 0 := by
    intro h
    rw [hw₀, Prod.mk_eq_zero] at h
    obtain ⟨h1, h2⟩ := h
    exact hℓ0 (Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2))
  set v₀ : ℤ × ℤ := (-ℓ.2, ℓ.1) with hv₀
  have hv₀prim : Primitive v₀ := by
    obtain ⟨a, b, hab⟩ := hℓprim
    exact ⟨-b, a, by simp only [hv₀]; linear_combination hab⟩
  have hv₀ne : v₀ ≠ 0 := hv₀prim.ne_zero
  have hw₀v₀ : inner2 w₀ v₀ = 0 := by
    simp only [inner2, hw₀, hv₀]; push_cast; ring
  have hdotv₀ : Nivat.LE2.dot ℓ v₀ = 0 := by simp only [Nivat.LE2.dot, hv₀]; ring
  -- ### orientation normalisation (集成者 2026-09-24): export `dir nℓ`, never plain `dir ℓ`
  -- The `by_cases hle` below picks only the *partner normal* `nℓ` (`ℓ` in one branch, `-ℓ` in
  -- the other) while `v₀ = dir ℓ` is branch-independent, so a naive export would carry
  -- `0 < det nℓ vl` in one branch and `det nℓ vl < 0` in the other.  `Nivat.ColleOrient`
  -- (`OrientationFree.lean`) proves that bit is not a function of `ξ` and is not recoverable
  -- from the exported interface, so it is pinned *here*, at the producer: the `¬hle` branch
  -- exports `-v₀ = dir (-ℓ)` in place of `v₀`, and then both branches satisfy
  -- `det nℓ vl = ‖nℓ‖² > 0` by the same computation.  Every `vl`-mentioning conjunct of the
  -- conclusion is `vl ↦ -vl` invariant (`ColleOrient.preamble_output_vl_neg`), so the swap is
  -- free.  What the new conjunct buys downstream is `dir vl = -nℓ`, `0 < det vl w`, and
  -- `det u' vl = -1`; see the "orientation normalisation" section of `exists_preamble`'s
  -- docstring above, including the ⚠ that the first version of that paragraph named the wrong
  -- consumer (`Hole3Room.nlmax_of_wadj`'s `hmvl` is about the *cut* normal `m`, already
  -- discharged by the tower package at `hmvl`（本文件 `:1949` 的 `obtain`）).
  have hℓcoord : ℓ.1 ≠ 0 ∨ ℓ.2 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hℓ0 (Prod.ext hc.1 hc.2)
  have hdetv₀ : det ℓ v₀ = ℓ.1 * ℓ.1 + ℓ.2 * ℓ.2 := by simp only [det, hv₀]; ring
  have hdetpos : 0 < det ℓ v₀ := by
    rw [hdetv₀]
    rcases hℓcoord with h1 | h2
    · nlinarith [mul_self_nonneg ℓ.2, mul_self_pos.mpr h1]
    · nlinarith [mul_self_nonneg ℓ.1, mul_self_pos.mpr h2]
  have hnv₀ne : (-v₀) ≠ 0 := neg_ne_zero.mpr hv₀ne
  have hnv₀prim : Primitive (-v₀) := by
    obtain ⟨a, b, hab⟩ := hv₀prim
    exact ⟨-a, -b, by simp only [Prod.fst_neg, Prod.snd_neg]; linear_combination hab⟩
  have hdotnv₀ : Nivat.LE2.dot ℓ (-v₀) = 0 := by
    simp only [Nivat.LE2.dot, Prod.fst_neg, Prod.snd_neg] at hdotv₀ ⊢
    linear_combination -hdotv₀
  have hdotnegnv₀ : Nivat.LE2.dot (-ℓ) (-v₀) = 0 := by
    simp only [Nivat.LE2.dot, Prod.fst_neg, Prod.snd_neg] at hdotv₀ ⊢
    linear_combination hdotv₀
  have hdetposneg : 0 < det (-ℓ) (-v₀) := by
    have h : det (-ℓ) (-v₀) = det ℓ v₀ := by
      simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
    rw [h]; exact hdetpos
  have honed₀ : ∃ y ∈ orbitClosure ξ, ∃ y' ∈ orbitClosure ξ, y ≠ y' ∧
      ∀ z : ℤ × ℤ, 0 ≤ inner2 w₀ z → y z = y' z := by
    obtain ⟨x, y, hx, hy, hne, hagr⟩ := hℓ_neg
    refine ⟨x, hx, y, hy, hne, fun z hz => hagr z ?_⟩
    rw [Nivat.LE2.dot_neg_left]
    rw [hw₀form] at hz
    have : (0 : ℤ) ≤ Nivat.LE2.dot ℓ z := by exact_mod_cast hz
    linarith
  have honed₁ : ∃ y ∈ orbitClosure ξ, ∃ y' ∈ orbitClosure ξ, y ≠ y' ∧
      ∀ z : ℤ × ℤ, 0 ≤ inner2 (-w₀) z → y z = y' z := by
    obtain ⟨x, y, hx, hy, hne, hagr⟩ := hℓ_pos
    refine ⟨x, hx, y, hy, hne, fun z hz => hagr z ?_⟩
    rw [Nivat.R2.inner2_neg_left, hw₀form] at hz
    have : ((Nivat.LE2.dot ℓ z : ℤ) : ℝ) ≤ 0 := by linarith
    exact_mod_cast this
  obtain ⟨S, hSgen, -, hdef⟩ := Nivat.R2.exists_generatingSet_biOriented hfin hlow
  have hSne : S.Nonempty := hSgen.1
  obtain ⟨zmin, hzminS, hzmin⟩ := S.exists_min_image (fun z => inner2 w₀ z) hSne
  obtain ⟨zmax, hzmaxS, hzmax⟩ := S.exists_max_image (fun z => inner2 w₀ z) hSne
  set cmin : ℝ := inner2 w₀ zmin with hcmin
  set cmax : ℝ := inner2 w₀ zmax with hcmax
  have hmin : ∀ z ∈ S, cmin ≤ inner2 w₀ z := hzmin
  have hmax : ∀ z ∈ S, inner2 w₀ z ≤ cmax := hzmax
  have hfmin : (S.filter fun z => inner2 w₀ z = cmin).Nonempty :=
    ⟨zmin, Finset.mem_filter.mpr ⟨hzminS, rfl⟩⟩
  have hfmax : (S.filter fun z => inner2 w₀ z = cmax).Nonempty :=
    ⟨zmax, Finset.mem_filter.mpr ⟨hzmaxS, rfl⟩⟩
  obtain ⟨hcount_max, hcount_min⟩ := hdef w₀ cmax cmin hmax hfmax hmin hfmin
  -- ### the orientation-free core, now on **both** members of the pair
  have core : ∀ (w' : ℝ × ℝ) (c c' : ℝ), w' ≠ 0 → inner2 w' v₀ = 0 →
      (∀ z ∈ S, c ≤ inner2 w' z) → (∀ z ∈ S, inner2 w' z ≤ c') →
      (S.filter fun z => inner2 w' z = c).Nonempty →
      (S.filter fun z => inner2 w' z = c).card ≤ (S.filter fun z => inner2 w' z = c').card →
      P ξ S - P ξ (S.filter fun z => c < inner2 w' z) ≤
        (S.filter fun z => inner2 w' z = c).card - 1 →
      (∃ y ∈ orbitClosure ξ, ∃ y' ∈ orbitClosure ξ, y ≠ y' ∧
        ∀ z : ℤ × ℤ, 0 ≤ inner2 w' z → y z = y' z) →
      ∃ (xper yper : Config ℤ) (p q gen : ℤ × ℤ),
        xper ∈ orbitClosure ξ ∧ yper ∈ orbitClosure ξ ∧
        Nivat.Colle.GeneratesAt ξ S gen ∧
        p ∈ Per xper ∧ p ≠ 0 ∧ det p v₀ = 0 ∧ q ∈ Per yper ∧ q ≠ 0 ∧ det q v₀ = 0 ∧
        (∃ g ∈ S, inner2 w' g = c ∧ xper g ≠ yper g) ∧
        ∀ z : ℤ × ℤ, c < inner2 w' z → xper z = yper z := by
    intro w' c c' hw' hw'v hmin' hmax' hfc' hle' hcount' honed'
    -- the period step (2.10 then 2.12), for any ambiguous member of `X_η`
    have perStep : ∀ x ∈ orbitClosure ξ,
        Nivat.Colle.AmbiguousAlong ξ (S.filter fun z => c < inner2 w' z) S x v₀ →
        ∃ p : ℤ × ℤ, p ∈ Per x ∧ p ≠ 0 ∧ det p v₀ = 0 := by
      intro x hx hamb
      obtain ⟨u, hu0, huw, huper⟩ := Nivat.Colle.colle_prop_2_10 hfin hx hSgen hv₀prim hw' hw'v
        hmin' hmax' hfc' hle' hcount' honed' hamb
      obtain ⟨n, hdec⟩ : ∃ n, PeriodicDecompZ x n := by
        by_cases hper : IsPeriodic x
        · exact ⟨1, fun _ => x, fun _ => hper, fun z => by simp⟩
        · obtain ⟨n, hord, -⟩ := hξ.2
          exact ⟨n, ((hξ.of_mem_orbitClosure hx hper).2 n hord).1⟩
      have hw'ne : -w' ≠ 0 := neg_ne_zero.mpr hw'
      have huw' : inner2 (-w') u = 0 := by rw [Nivat.R2.inner2_neg_left, huw, neg_zero]
      have hlocal : ∀ z, -c ≤ inner2 (-w') z → x (z + u) = x z := by
        intro z hz
        apply huper
        rw [Nivat.R2.inner2_neg_left] at hz
        linarith
      obtain ⟨k, hk, hkper⟩ :=
        Nivat.Colle.period_multiple_of_periodicDecompZ hdec hw'ne hu0 huw' hlocal
      refine ⟨k • u, hkper, zsmul_ne_zero_of_ne_zero hk hu0, ?_⟩
      have hkw : inner2 w' (k • u) = 0 := by rw [inner2_zsmul, huw, mul_zero]
      exact Nivat.Colle.det_eq_zero_of_inner2_eq_zero hw' hkw hw'v
    -- `b3_colle2.txt:774`: the ambiguous pair `x_per, y_per`
    obtain ⟨x, hx, x', hx', hamb, hamb', hg, hab⟩ :=
      Nivat.Colle.exists_ambiguousPair_of_oneSidedNonexpansive hSgen hv₀prim hw' hw'v hmin'
        hfc' honed'
    obtain ⟨p, hp, hp0, hpv⟩ := perStep x hx hamb
    obtain ⟨q, hq, hq0, hqv⟩ := perStep x' hx' hamb'
    obtain ⟨a, haF, hamin⟩ :=
      (S.filter fun z => inner2 w' z = c).exists_min_image (fun z => Nivat.Colle.dotZ z v₀) hfc'
    obtain ⟨haS, hac⟩ := Finset.mem_filter.mp haF
    have hgenA : Nivat.Colle.GeneratesAt ξ S a :=
      Nivat.Colle.generatesAt_of_min_on_face hSgen hv₀prim hw' hw'v hmin' haS hac
        (fun z hz hzc => hamin z (Finset.mem_filter.mpr ⟨hz, hzc⟩))
    exact ⟨x, x', p, q, a, hx, hx', hgenA, hp, hp0, hpv, hq, hq0, hqv, hg, hab⟩
  -- ### the WLOG `:890`, at the face line, in either orientation
  -- `m` is the integer normal (`ℓ` or `-ℓ`), `wm` its real form, `cr` the real face level, and
  -- `vm` the exported tangent — `dir m`, i.e. `v₀` when `m = ℓ` and `-v₀` when `m = -ℓ`.  Taking
  -- `vm` as a parameter (rather than always `v₀`) is the orientation normalisation: it is what
  -- lets both branches discharge the `0 < det m vm` conjunct by the same computation.
  have finish : ∀ (m vm : ℤ × ℤ) (wm : ℝ × ℝ) (cr : ℝ), m ≠ 0 → Primitive m →
      vm ≠ 0 → Primitive vm → Nivat.LE2.dot ℓ vm = 0 →
      Nivat.LE2.dot m vm = 0 → 0 < det m vm →
      (∀ z : ℤ × ℤ, inner2 wm z = ((Nivat.LE2.dot m z : ℤ) : ℝ)) →
      ∀ (xper yper : Config ℤ) (p q gen : ℤ × ℤ),
        xper ∈ orbitClosure ξ → yper ∈ orbitClosure ξ →
        Nivat.Colle.GeneratesAt ξ S gen →
        p ∈ Per xper → p ≠ 0 → det p vm = 0 → q ∈ Per yper → q ≠ 0 → det q vm = 0 →
        (∃ g ∈ S, inner2 wm g = cr ∧ xper g ≠ yper g) →
        (∀ z : ℤ × ℤ, cr < inner2 wm z → xper z = yper z) →
      ∃ (xper : Config ℤ) (vl p : ℤ × ℤ) (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ),
        xper ∈ orbitClosure ξ ∧ Nivat.Colle.GeneratesAt ξ S gen ∧
        Nivat.Colle.IsGeneratingSet ξ S ∧
        p ∈ Per xper ∧ p ≠ 0 ∧ vl ≠ 0 ∧ Primitive vl ∧ det p vl = 0 ∧
        Nivat.LE2.dot ℓ vl = 0 ∧
        (∃ (yper : Config ℤ) (nℓ : ℤ × ℤ) (cz : ℤ) (g : ℤ × ℤ),
          yper ∈ orbitClosure ξ ∧ xper ≠ yper ∧
          nℓ ≠ 0 ∧ Primitive nℓ ∧ Nivat.LE2.dot nℓ vl = 0 ∧ 0 < det nℓ vl ∧
          (∀ z : ℤ × ℤ, cz < Nivat.LE2.dot nℓ z → xper z = yper z) ∧
          Nivat.LE2.dot nℓ g = cz ∧ xper g ≠ yper g ∧
          ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
            PeriodicOnWith xper {z | cz ≤ Nivat.LE2.dot nℓ z} h ∧
            PeriodicOnWith xper {z | cz ≤ Nivat.LE2.dot nℓ z} h') ∧
        ∀ (n : ℝ × ℝ) (cmax cmin : ℝ),
          (∀ z ∈ S, inner2 n z ≤ cmax) → (Nivat.R2.face S n cmax).Nonempty →
          (∀ z ∈ S, cmin ≤ inner2 n z) → (Nivat.R2.face S n cmin).Nonempty →
            P ξ S - P ξ (S.filter fun z => inner2 n z < cmax) ≤
              (Nivat.R2.face S n cmax).card - 1 ∧
            P ξ S - P ξ (S.filter fun z => cmin < inner2 n z) ≤
              (Nivat.R2.face S n cmin).card - 1 := by
    intro m vm wm cr hm0 hmprim hvm0 hvmprim hvmℓ hmv hmdet hform xper yper p q gen hx hy hgen
      hp hp0 hpv hq hq0 hqv hg hab
    obtain ⟨g, -, hgc, hgne⟩ := hg
    -- the face line is a lattice level: `cr = dot m g`
    have hcr : cr = ((Nivat.LE2.dot m g : ℤ) : ℝ) := by rw [← hgc, hform]
    have hab' : ∀ z : ℤ × ℤ, Nivat.LE2.dot m g < Nivat.LE2.dot m z → xper z = yper z := by
      intro z hz
      apply hab
      rw [hform, hcr]
      exact_mod_cast hz
    obtain ⟨xper', yper', p', hx', hy', hp', hp0', hpv', hab'', hgz, hgne', hnotDP⟩ :=
      Nivat.Colle35.wlog_notDP hx hy hp hp0 hpv hq hq0 hqv hm0 hab' rfl hgne
    exact ⟨xper', vm, p', S, gen, hx', hgen, hSgen, hp', hp0', hvm0, hvmprim, hpv', hvmℓ,
      ⟨yper', m, Nivat.LE2.dot m g, g, hy', fun h => hgne' (by rw [h]), hm0, hmprim, hmv, hmdet,
        hab'', hgz, hgne', hnotDP⟩,
      hdef⟩
  by_cases hle : (S.filter fun z => inner2 w₀ z = cmin).card ≤
      (S.filter fun z => inner2 w₀ z = cmax).card
  · obtain ⟨xper, yper, p, q, gen, hx, hy, hgen, hp, hp0, hpv, hq, hq0, hqv, hg, hab⟩ :=
      core w₀ cmin cmax hw₀ne hw₀v₀ hmin hmax hfmin hle hcount_min honed₀
    exact finish ℓ v₀ w₀ cmin hℓ0 hℓprim hv₀ne hv₀prim hdotv₀ hdotv₀ hdetpos hw₀form xper yper
      p q gen hx hy hgen hp hp0 hpv hq hq0 hqv hg hab
  · push_neg at hle
    have hℓnegprim : Primitive (-ℓ) := by
      obtain ⟨a, b, hab⟩ := hℓprim
      exact ⟨-a, -b, by simp only [Prod.fst_neg, Prod.snd_neg]; linear_combination hab⟩
    have hface_max : (S.filter fun z => inner2 (-w₀) z = -cmax)
        = S.filter fun z => inner2 w₀ z = cmax := Nivat.R2.face_neg_level S w₀ cmax
    have hface_min : (S.filter fun z => inner2 (-w₀) z = -cmin)
        = S.filter fun z => inner2 w₀ z = cmin := Nivat.R2.face_neg_level S w₀ cmin
    have hmin' : ∀ z ∈ S, -cmax ≤ inner2 (-w₀) z := by
      intro z hz; rw [Nivat.R2.inner2_neg_left]; linarith [hmax z hz]
    have hmax' : ∀ z ∈ S, inner2 (-w₀) z ≤ -cmin := by
      intro z hz; rw [Nivat.R2.inner2_neg_left]; linarith [hmin z hz]
    have hfmin' : (S.filter fun z => inner2 (-w₀) z = -cmax).Nonempty := by
      rw [hface_max]; exact hfmax
    have hle' : (S.filter fun z => inner2 (-w₀) z = -cmax).card ≤
        (S.filter fun z => inner2 (-w₀) z = -cmin).card := by
      rw [hface_max, hface_min]; exact hle.le
    have hQ : (S.filter fun z => -cmax < inner2 (-w₀) z)
        = S.filter fun z => inner2 w₀ z < cmax := by
      refine Finset.filter_congr fun z _ => ?_
      rw [Nivat.R2.inner2_neg_left]
      constructor <;> intro h <;> linarith
    have hcount' : P ξ S - P ξ (S.filter fun z => -cmax < inner2 (-w₀) z) ≤
        (S.filter fun z => inner2 (-w₀) z = -cmax).card - 1 := by
      rw [hface_max, hQ]; exact hcount_max
    have hw₀v₀' : inner2 (-w₀) v₀ = 0 := by rw [Nivat.R2.inner2_neg_left, hw₀v₀, neg_zero]
    have hnegform : ∀ z : ℤ × ℤ, inner2 (-w₀) z = ((Nivat.LE2.dot (-ℓ) z : ℤ) : ℝ) := by
      intro z
      rw [Nivat.R2.inner2_neg_left, hw₀form, Nivat.LE2.dot_neg_left]
      push_cast; ring
    obtain ⟨xper, yper, p, q, gen, hx, hy, hgen, hp, hp0, hpv, hq, hq0, hqv, hg, hab⟩ :=
      core (-w₀) (-cmax) (-cmin) (neg_ne_zero.mpr hw₀ne) hw₀v₀' hmin' hmax' hfmin' hle'
        hcount' honed₁
    -- orientation normalisation: this branch's normal is `-ℓ`, so the exported tangent is
    -- `-v₀ = dir (-ℓ)`; see the `have hdetpos` block above.
    have hpvn : det p (-v₀) = 0 := by
      simp only [det, Prod.fst_neg, Prod.snd_neg] at hpv ⊢
      linear_combination -hpv
    have hqvn : det q (-v₀) = 0 := by
      simp only [det, Prod.fst_neg, Prod.snd_neg] at hqv ⊢
      linear_combination -hqv
    exact finish (-ℓ) (-v₀) (-w₀) (-cmax) (neg_ne_zero.mpr hℓ0) hℓnegprim hnv₀ne hnv₀prim
      hdotnv₀ hdotnegnv₀ hdetposneg hnegform xper yper p q gen hx hy hgen
      hp hp0 hpvn hq hq0 hqvn hg hab

/-- **Sign-normalisation of the period `p` against the chain direction `vl`** (集成者 2026-09-23).

`exists_preamble_pair` (`:783`) exports `p ∈ Per xper`, `p ≠ 0`, `Primitive vl` and
`det p vl = 0`.  All three `p`-conjuncts are invariant under `p ↦ -p`, because `Per xper` is an
`AddSubgroup (ℤ × ℤ)` (`Defs/Config.lean:62`), so the producer may always hand down the
**negative** multiple.  `det p vl = 0` with `vl` primitive forces `p = k • vl`
(`eq_zsmul_of_det_eq_zero`, `Lattice/Primitive.lean:83`), and `p ≠ 0` forces `k ≠ 0`; the
statement below just picks the sign.

**消费者**：`exists_chainData`（本文件同名 `theorem`；§85 旧注记 `:1145`，2026-09-24 实测已腐烂，
当时实际在 `:1341`——改记标识符，行号在它上方每次改动后都会再腐）的 `hp_neg` binder。那条 binder 不是我们凭空加强的——
`tmp/wip/LeafAAssemble.lean:1001-1019` 用 `hstep`（帽子并集对 `-vl` 封闭）迭代 `c` 次来证
`rec_p`，而 `+vl` 方向没有对应的封闭性，所以 `p` 必须是 `vl` 的**负**整数倍。
在本轮之前 `hp_neg` 在 `Nivat/**.lean` 里**没有任何生产者**（`grep` 实测），
于是 leaf A 的装配体关掉的是一条比链上弱的命题；这条引理就是把那个落差补上。 -/
theorem exists_neg_multiple_of_perp {xper : Config ℤ} {vl p : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hp_mem : p ∈ Per xper) (hp_ne : p ≠ 0)
    (hdet_vl : det p vl = 0) :
    ∃ p' : ℤ × ℤ, p' ∈ Per xper ∧ p' ≠ 0 ∧ det p' vl = 0 ∧
      ∃ c : ℕ, 0 < c ∧ p' = -(c : ℤ) • vl := by
  have hdet' : det vl p = 0 := by rw [det_comm vl p, hdet_vl, neg_zero]
  obtain ⟨k, hk⟩ := eq_zsmul_of_det_eq_zero hvl_prim hdet'
  have hk0 : k ≠ 0 := by
    intro h
    exact hp_ne (by rw [hk, h, zero_smul])
  rcases lt_or_gt_of_ne hk0 with hneg | hpos
  · refine ⟨p, hp_mem, hp_ne, hdet_vl, (-k).toNat, by omega, ?_⟩
    have hcast : -(((-k).toNat : ℤ)) = k := by omega
    rw [hk, hcast]
  · refine ⟨-p, neg_mem hp_mem, neg_ne_zero.mpr hp_ne, ?_, k.toNat, by omega, ?_⟩
    · simp only [det, Prod.fst_neg, Prod.snd_neg]
      simp only [det] at hdet_vl
      linear_combination -hdet_vl
    · have hcast : ((k.toNat : ℤ)) = k := by omega
      rw [hk, hcast, neg_smul]

/-- **Colle's §3 chain construction**, with `Env` pinned, the chain direction tied to `ℓ`, and
the region geometry of `ChainGeom.lean` attached.

⚠ **Case 2 only** (`hcase2`).  Collé reaches Lemma 3.5 only in Case 2 (`b3_colle2.txt:760`),
and `hcase2` is the "but ≠" half of Lemma 3.5(i)'s hypothesis (`b3_colle2.txt:426-430`).
Before 2026-09-17 this theorem asserted the chain unconditionally, which is strictly stronger
than anything Collé proves; see `blueprint/NOTE.md`
「`exists_chainData` 吞掉了 Lemma 4.5 的 Case 2 前提」.

Five things are demanded of the output, and each is load-bearing:

* `c.Env = Nivat.LE2.EnvOf ↑d.Sphi` — the instruction of §10 of `LatticeEdges.lean`, with
  the set being `𝒮_φ` (`d : DecompDataZ ξ`, `b3_colle2.txt:298`), **not** the Lemma 2.4 set
  `S` of `exists_preamble` (see "Which set" above).  The `S` index of the output `ChainData`
  is `d.Sphi` for the same reason: Lemma 3.5 (`:424`) is stated over `φ ∈ ann(η)` and the
  edges of `𝒮_φ`, and `Lemma35.lean:669-670` names its `S` "`S_φ`".
  `Lemma35.lean` leaves `Env` abstract, so a `ChainData` can be built with
  `Env := fun _ => True`, under which `envB`/`envA`/`maximalHat` say nothing.  Pinning it
  makes those fields carry Colle's Definition 3.2.
* `∀ i, c.B i ⊂ c.B (i + 1)` — the chain actually grows.  Without it the degenerate
  `B i = {0}` chain of `Nivat.Colle35.nonempty_chainData` satisfies the statement and
  `Â_∞` is a point.
* `dot ℓ vl = 0` — the chain runs along the line `{dot ℓ · = 0}`; `ℓ` is its normal.  See
  joint 1 in the module docstring for why this is `dot` and not `det`.
* the output is a `Nivat.Colle35.ChainDataGeom`, not a bare `ChainData` — the shell formula
  `b3_colle2.txt:440` plus the `ℓ_J`-edge geometry.  See joint 3.  Its `gen` index is the
  existential `genφ`, together with `GeneratesAt ξ d.Sphi genφ`: the site `gen` of
  `exists_preamble` generates for the Lemma 2.4 set `S`, not for `𝒮_φ`, so it cannot be
  reused.  (`Nivat.Colle.IsGeneratingSet ξ d.Sphi`, Collé's "`𝒮_φ` is `η`-generating" in the
  form Claim 3.7 consumes, is no longer an output: it is `d.isGeneratingSet`.)
* `hgen`, `hSgen`, `hdef` and with them the Lemma 2.4 set `S` are **no longer inputs**
  (2026-09-17).  They were in scope at the hole, so dropping them is a strengthening the
  file contract allows; it was ruled mandatory because a dangling `S` in an unproved
  statement is exactly the shape that let the `decomp.Sphi = S` fiat survive — "harmless to
  typechecking" is the property that hid it.  §3 never uses Lemma 2.4's set: Lemma 3.5
  (`:424-430`) and Claim 3.7 (`:597`) run on `𝒮_φ` alone.  Lemma 2.4 set reaches Claim 4.11
  through the `Sgen`/`hSgen` binder of `region_periods_and_rays` (2026-09-17); `hdef` will follow.
**Not** `DoublyPeriodic xper`.  It was added here on 2026-09-17 citing `b3_colle2.txt:539`
and withdrawn the same day: `:539` lives under the §3.1 contradiction hypothesis `:537`,
which the `hw₁`/`hw₂` below negate, and §4 Case 2 assumes its negation outright (`:890`).
That was the third time the same conjunct entered the tree; see `blueprint/NOTE.md`
「`DoublyPeriodic xper` 第三次入侵」 and joint 4.

`ColleRegion.envOf_chain_nondegenerate` shows the first two demands are jointly satisfiable
in isolation, so neither is vacuous and together they are not self-contradictory.

## What the existing `ChainData` witnesses do and do not say about this (measured 2026-09-14)

`Lemma35Wiring.lean` is not imported by anything, but it holds the only two `ChainData`
witnesses in the tree, and both bear directly on this statement.  Read carefully, they
constrain it less than their docstrings suggest, because in **both** the `Env` predicate is
built from a *different* set than the index `S`:

| witness | `S` | `Env` | status |
|---|---|---|---|
| ~~`chainData_wired_but_incomplete`~~ | — | — | **withdrawn 2026-09-16, row void** |
| `chainB` | `{(0,0),(1,0)}` | `EnvOf sq1` | all 19 obligations, `sorry`-free |

* The first row is struck because the theorem no longer exists (`Lemma35Wiring.lean:174`,
  "A theorem `chainData_wired_but_incomplete` stood here"), and the status it reported was
  wrong in the opposite direction from what the row suggests: per `Lemma35Wiring.lean:179-181`
  its statement was *literally* that of `nonempty_chainData` (`Lemma35.lean:768-770`), which is
  **proved** and closes over `[propext, Classical.choice, Quot.sound]`.  So there is no
  refutation to inherit here, and the surviving informative content is `maximalHat_wired_refuted`
  alone.
* `chainB` is a complete, non-degenerate `ChainData` with a strictly growing chain — but
  `c.Env = EnvOf sq1` while `↑S = {(0,0),(1,0)}`, so it does **not** satisfy `c.Env = EnvOf ↑S`
  and is not a witness for the conjunction demanded here.
* `maximalHat_wired_refuted` (`Nivat.Colle35`, `Lemma35Wiring.lean:202`) is a machine-checked
  `False` (closure `[propext, Classical.choice, Quot.sound]`), and its docstring argues on paper
  that the obstruction is structural.  But it too is at a mismatched pair (`S = {0}`,
  `Env = EnvOf sq1`), so it does **not** refute the matched pinning either.  Its actual content
  is narrower than "the pinning is impossible": it says that when `η` and `x_per` differ at a
  *single point*, the agreement clause of `maximalHat` can forbid only that point, so `Â_0` can
  be enlarged past it.
  ⚠ An earlier version of this paragraph justified the enlargement by "`Enveloped` has no
  convexity requirement".  That is **false**: `Enveloped` (`LatticeEdges.lean:628`) unfolds to
  `WeaklyEnveloped` (`:624`), whose *first* conjunct is `IsLatticeConvexRegion T` — see
  `WeaklyEnveloped.latticeConvex` (`:633`).  Convexity was restored in ea5bbc5 and this note was
  not updated.  The kernel result at `:202` is unaffected; what is retracted is only the stated
  reason for it, which has not been re-derived.  Do not cite the enlargement step from here.
* `chainB` escapes exactly by making `η` and `x_per` differ on a whole wall — which is what
  Colle's construction does.

So: no witness in the tree satisfies `c.Env = EnvOf ↑S` with matching `S` together with the
full 19 obligations, and none refutes it.  `envOf_chain_nondegenerate` is the only evidence
at a *matched* pair (`S := winS`, `↑winS = sq1`), and it covers only the `Env` and growth
clauses, not the other 17 fields.  Whoever takes this theorem should expect `maximalHat` to
be where it is decided, and should make `η` disagree with `x_per` along a wall, not a point.

What is missing is the construction of such a chain from `ξ` itself: the convex-geometry
content of Colle §3 (the maximality of the enveloped sets `A_i`, the shell families
`Â_i^{(ε)}`, the distance enumeration `0 = d₀ < d₁ < ⋯`, and the generation filtration).  The
last three of those are now in `MaximalEnveloped.lean`; the maximality is the open one, and
`MaximalEnveloped.no_maximal_enveloped_halfStrip` shows why — inside a half-strip the
enveloped family has *no* maximal element, so the agreement clause carries the whole
weight.

**Corrected 2026-09-18: this used to read "maximal enveloped sets via Zorn", which attributed
to Collé an argument he does not give.**  `Zorn` occurs **zero** times in `b3_colle2.txt`
(verified by grep); `maximal` occurs at `:484` (the assertion itself, ordered by inclusion,
with four conditions including the agreement clause), `:492` (the *transported* statement for
`Â_i`, prefaced "It is easy to see"), `:530` (the consumer), and `:760`/`:852`/`:858` in §4
about an unrelated maximal integer `N`.  There is no chain-upper-bound argument and no appeal
to Zorn or Hausdorff maximality anywhere in the paper.  Whoever discharges this `sorry` must
therefore **invent** the maximality argument rather than transcribe one — a different and
better-defined task than "formalize §3 item (iv)".

## `hpartner`, and the `nfp_L` obligation it pays for (2026-09-18)

`hpartner` is the ambiguity partner `y_per` of `b3_colle2.txt:774`, exported by
`exists_preamble` on the same day.  It is here because `ChainDataGeom.nfp_L`
(`ChainGeom.lean:171`) — Collé's Case 2 standing assumption *"`x_per|ℋ(ℓ^(−))` is not fully
periodic"* (`b3_colle2.txt:890`) — is a field of the bundle this theorem produces, and the
level it is stated at, `cL`, is the bundle's own `ℓ_ι`-support value (see that field's
docstring for why `cL` is forced and cannot be lowered).

So the discharge runs: `Colle35.not_doublyPeriodicOn_both` (`HalfPlaneDoublyPeriodic.lean`,
proved, kernel-clean) refutes *both* `x_per` and `y_per` being doubly periodic on the half
plane, given a point of that half plane where they disagree; whoever builds the chain then
picks the member that is not, and — this is the extra burden — must **place `Â_∞` so that its
`ℓ_ι`-support line carries a disagreement point of the pair**.  `hpartner` supplies the pair
and its agreement half plane `{cz ≤ ⟪nℓ, ·⟫}`; the placement is on the construction.

The orientation is carried by the bound vector `nℓ` (`nℓ ≠ 0`, `dot nℓ vl = 0`) rather than by
an inequality about `𝒮`, for the reason given in `exists_preamble`'s "Orientation" section:
exporting the inequality would push the `R2Orientation.lean` gap onto callers.

## item (ii) 的生产者（接链，2026-09-21）

这条 `sorry` 欠的**不是字段，是递归本身**：`ChainRecursion` 的 `B (i+1) := A i` 在有限种子上
产不出任何 `ChainDataGeom`，唯一剩下的逃生阀是 Collé item (ii)（`b3_colle2.txt:474-476`，
`B_i` **同时**含 `A_{i-1}` 与 `[-i+1, i-1]² ∩ ℋ(ℓ^(−))`）。该存在性现已在主仓：

* `Nivat.EnvSuperset.exists_enveloped_superset_pair` (`EnvSuperset.lean:366`) ——
  给定 `PosArea 𝒮_φ` 与两个有限集 `A`、`Box`，产出一个同时包含二者的 `E(𝒮_φ)`-enveloped `B`。
* 调用点的 `PosArea` 实参是 `Nivat.AhatMono.posArea_Sphi d.toDecompData` (`AhatMono.lean:3175`)，
  即 `Nivat.EnvSuperset.exists_enveloped_superset_pair d.toDecompData.Sphi`
  `(Nivat.AhatMono.posArea_Sphi d.toDecompData) hAfin hBoxfin`。

⚠ **读法限定**：这只关掉 item (ii) 的**存在性**一半；`ChainRecursion` 里把 `B (i+1) := A i`
换成这个产物、再重证 `itemII_ch` / `exhausts_ch` 的那一步**还没做**，所以本 `sorry` 未动。
本节写在这里是为了让 `EnvSuperset` 进主定理的可达闭包（硬规矩 9），不是宣称已证。

**第 210 轮补一格：调用 `ItemIIRecursion.exists_itemII_recursion` 不需要新几何输入。**
它的十一条前提里有两条不在本 `theorem` 的上下文里点名（`hnℓ' : -nℓ ∈ E ↑S`，以及整个
`{n m} (hdet : det n m ≠ 0)` 四membership 组），此前不知道补它们要不要新代价。
`Nivat.ItemIIFeed.nonempty_itemIIRecursionData_of_chainData_binders` (`ItemIIFeed.lean`) 只吃
本签名已有的 binder（`hpartner` 只拆出 `Primitive nℓ` 与 `dot nℓ vl = 0` 两支，
⛔ `0 < det nℓ vl` 不进，第 179 轮红线），产出 `ItemIIRecursionData`：两条都免费，
第一条花掉素法向的符号歧义，第二条花掉 `DecompData.hm : 2 ≤ m` 与 `h_dir`（原文 `:424`）。

⛔ **它同样不关本 `sorry`**：`exists_itemII_recursion` 的结论是
`∃ _rd : ItemIIRecursionData …, True`，本 `theorem` 要的是 `ChainDataGeom`；shell 块
（`shellInf_sup` / `shellInf_union` / `shellInf_eq` / `shellSubStrip`）、`bottom`、`rec_p`
一个都不是 `ItemIIRecursionData` 的字段（`ItemIIRecursion.lean` §5 自己列的）。
关掉的是**可调用性**，不是 item (ii) ⟹ 本 `sorry`。 -/
theorem exists_chainData (hξ : IsMinimalCounterexample ξ) (d : DecompDataZ ξ)
    {w : ℝ × ℝ} (hw : w ≠ 0) (hw₁ : w ∈ ONED ξ) (hw₂ : -w ∈ ONED ξ)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_pos : Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hxper : xper ∈ orbitClosure ξ)
    (hp_mem : p ∈ Per xper) (hp_ne : p ≠ 0) (hvl_ne : vl ≠ 0) (hvl_prim : Primitive vl)
    (hdet_vl : det p vl = 0) (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0)
    -- **Added 2026-09-23 (集成者).**  `p` is a *negative* integer multiple of `vl`.  This is not
    -- an extra mathematical assumption: `det p vl = 0` + `Primitive vl` + `p ≠ 0` already force
    -- `p = k • vl` with `k ≠ 0`, and the sign is the producer's free choice because `Per xper`
    -- is an `AddSubgroup` — discharged at the call site (`ColleRegion.lean:364`) by
    -- `exists_neg_multiple_of_perp` (`:1002`), which normalises `exists_preamble_pair`'s `p`.
    -- The consumer of the sign is `rec_p`: leaf A derives `g + p ∈ ⋃ᵢ Âᵢ` by iterating the
    -- `-vl`-closure of the hat union `c` times (`tmp/wip/LeafAAssemble.lean:1001-1019`), and the
    -- `+vl` direction has no such closure.  Before this round the binder had **no** producer in
    -- `Nivat/**.lean`, so the leaf-A assembly was closing a strictly weaker statement than this.
    (hp_neg : ∃ c : ℕ, 0 < c ∧ p = -(c : ℤ) • vl)
    -- **Strengthened 2026-09-19** to the export of `exists_preamble_pair` (`:658`).  The old
    -- form agreed on the *closed* half plane `cz ≤ dot nℓ z` and named no disagreement point;
    -- the new one agrees only strictly above `cz`, pins a disagreement point `g` **on** the
    -- level line, and adds Collé's `b3_colle2.txt:890` WLOG that `xper` is not doubly periodic
    -- there.  That last conjunct is what `nfp_L` needs and what no earlier signature could
    -- state; `Colle35.wlog_notDP` (`HalfPlaneDoublyPeriodic.lean:315`) discharges it on the
    -- producer side.  Free at the call site (`ColleRegion.lean:363`).
    (hpartner : ∃ (yper : Config ℤ) (nℓ : ℤ × ℤ) (cz : ℤ) (g : ℤ × ℤ),
      yper ∈ orbitClosure ξ ∧ xper ≠ yper ∧
      nℓ ≠ 0 ∧ Primitive nℓ ∧ Nivat.LE2.dot nℓ vl = 0 ∧ 0 < det nℓ vl ∧
      (∀ z : ℤ × ℤ, cz < Nivat.LE2.dot nℓ z → xper z = yper z) ∧
      Nivat.LE2.dot nℓ g = cz ∧ xper g ≠ yper g ∧
      ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
        PeriodicOnWith xper {z | cz ≤ Nivat.LE2.dot nℓ z} h ∧
        PeriodicOnWith xper {z | cz ≤ Nivat.LE2.dot nℓ z} h')
    (hcase2 : Case2 ξ xper d.Sphi vl) :
    ∃ (genφ : ℤ × ℤ) (cg : ChainDataGeom ξ xper vl p d.Sphi genφ),
      Nivat.Colle.GeneratesAt ξ d.Sphi genφ ∧
      cg.toChainData.Env = Nivat.LE2.EnvOf (d.Sphi : Set (ℤ × ℤ)) := by
  -- Closed 2026-09-30: push-`J`-face shell route, `Hole1PushShell.lean`.
  exact exists_chainData_closed hξ d hw hw₁ hw₂ hℓ_nel hℓ_pos hℓ_neg hxper hp_mem hp_ne hvl_ne
    hvl_prim hdet_vl hdet_ℓ hp_neg hpartner hcase2

/-! **`exists_chainData` reduces to a single object: a populated `ChainDataGeomParts`.** (撤回，见文末)

This is the on-chain statement of what `Nivat.ChainAsm.Aparts.chainDataGeomParts_closes_twoConjunct_shape`
(⊘ 该标识符全树**定义数 = 0**，只在本文件散文里出现三次；旧引 ChainPartsFeed 的 `:372` 越界——该文件共
335 行。按本段下方 (0) 的「删号留名」已去号。⚠ 此处**故意不写成 `文件名.lean:行号` 形式**：
`scripts/anchors_outfile.py` 无法区分「正在使用的锚点」与「被引为已作废的锚点」，
写全形会让订正本身持续触发 RED（PROTOCOL §107）。2026-09-25 集成者订正) proves.  The point of restating it *here* is not the mathematics —
the proof is one application — but the **import direction**.  Until 2026-09-20 `ChainPartsFeed`
was transitively downstream of this file (via `ShellMink → Step_PeriodsRays2 → RegionSteps`),
so the assembly that closes `exists_chainData` could not be reached from `exists_chainData`.
Dropping one unused `import` in `ChainPartsFeed` (a `#check` receipt, nothing else) reversed the
direction and made this line possible.

**What it buys.**  The `sorry` below is now a *one-obligation* hole with a kernel witness to that
fact, not a prose claim: every one of `ofParts`'s 25 hypotheses, and the two conjuncts of the
conclusion, are discharged by `c` together with `d.isGeneratingSet`.  `GeneratesAt` comes from
`FaceBlock.generatesAt_a'`, `Env` by `rfl`, and `rec_vJ` for free from
`rec_vJ_of_exists_chainData_layer`.

⚠ **This is a reduction, not progress on the mathematics.**  No `ChainDataGeomParts` is inhabited
anywhere in the tree; `exists_chainData` is exactly as open as it was.  What changed is that the
remaining obligation is now *named, single, and on-chain*.  Per hard rule 1 the gate is unmoved.

🔴 **撤回 (2026-09-20, 集成者)：`exists_chainData_of_parts` 整条删除。**
它的证明体是 `Nivat.ChainAsm.Aparts.chainDataGeomParts_closes_twoConjunct_shape`，
而该定理在 `ChainPartsFeed.lean` 编译失败期间**依赖 `sorryAx`**，2026-09-20 由 Aparts
连同 `ChainDataGeomParts.toChainDataGeom` 一并删除。于是上面那段「一条义务的洞」的说法
**从来没有成立过**——它是一个 `sorryAx` 定理的转述，不是内核事实（`PROTOCOL.md` §15）。
本文件的 `sorry` 计数不变（`exists_chainData` 自己那条还在）；变的是不再有一条
链上定理假装它已被归约。`ChainDataGeomParts`（`ChainPartsFeed.lean:173`，24 个字段）
仍在且干净，重建 `toChainDataGeom` 需要逐字段对上 `ChainDataGeom.ofParts` 的 25 条前提。

══ 2026-09-24（第 197 轮，集成者）：上面两处引文已腐烂，连同本洞的**当前**残余一并订正 ══

**(0) §57 甲类行号／标识符腐烂。** 本段两次引用的
`Nivat.ChainAsm.Aparts.chainDataGeomParts_closes_twoConjunct_shape`（`ChainPartsFeed.lean`）
**在树中已不存在**——`ChainPartsFeed.lean` 全文件只有五条声明：
`rec_vJ_needs_hEnv_hyp` / `rec_vJ_of_exists_chainData_layer` / `ChainDataGeomParts`（`structure`）/
`ahatMono_field_of_extraction` / `A_mono_of_subBA_subAB`。
⚠⚠ **第 202 轮：本段自己也腐烂了，且腐烂的正是那句订正。** 上一版写「现共 327 行」「`:284`／`:303`」
「`ChainDataGeomParts` 的真实行号是 `:179`（不是 `:173`）」——**实测 334 行、`:291`／`:310`、`:186`**，
即「用来修行号的那句话」比被它修的行号漂得还多。⟹ 本段起**一律删号留名**（规矩 8 只要求带标识符名，
不要求带行号），定位用 `python scripts/declscan.py NAME`（§75；裸 `grep` 的老条文已废）。

**(1) 「重建 `toChainDataGeom`」这句也已过时——它早就重建好了。**
`Nivat.ChainAsm.Aparts.ChainDataGeomParts.toChainDataGeom`（`PartsToGeom.lean`）在树中，
随全量 build 通过，且是**诚实的 24+1 构造器**：结构体的 24 个字段逐一喂给 `ofParts`，
第 25 条 `rec_vJ : ∀ g ∈ ⋃ i, hatOf c.A c.kk vl i, g + c.vJ ∈ ⋃ i, hatOf c.A c.kk vl i`
**留成显式参数**，没有假装它自由。配套的 `Env = EnvOf` 那一半是同文件的 `toChainDataGeom_Env`。
⟹ 上面「`rec_vJ` for free from `rec_vJ_of_exists_chainData_layer`」那句**是假的**，
理由写在 `ChainPartsFeed.lean` 的 🔴 订正里（「Smart constructor」那节末尾）：后者的结论是
`IsLatticeConvexRegion (⋃ i, hatOf A kk vl i)`，而 `IsLatticeConvexRegion`
（`Section8/HalfPlane.lean:174`）**有界集照样满足**（取 `R = C = {(0,0)}`），
有界集对 `+vJ` 显然不封闭 ⟹ 前者不蕴含后者，平移不变性不可能从凸性单独得出。

**(2) ⟹ 本洞当前的残余，精确三条（不是「一条义务」，也不是「什么都没有」）。**
链条是：`exists_itemII_chain`（`ItemIIChain.lean:117`，**已证、在树中**）给出 `B, A, u`
连同 `envB` / `finB` / `maxA` / `subBA` / `subAB` / 盒子条款 / `ItemII` / `Exhausts`
（原文 `b3_colle2.txt:466-498`）⟹ 填 `ChainDataGeomParts` 的 24 个字段 ⟹ `toChainDataGeom`
⟹ `exists_chainData`。缺口是：
  * **(G-a) `rec_vJ`**（第 25 条，无生产者）；
  * **(G-b) `hext`**（`ahatMono_field_of_extraction`（`ChainPartsFeed.lean:284`）的 face-基数单调前提）——
    `ChainPartsFeed.lean:277` 明写它**独立**于 `hmono` ＋ `henv`（有反例），是 `AhatMono` 字段的活缺口；
  * **(G-c) `hkk`**（`kk` 的单调性）。
  其余字段有来路：`hmono` 由 `A_mono_of_subBA_subAB`（`:303`）从 `subBA`/`subAB` 复合而得，
  `gen_eq` 由 `FaceBlock.generatesAt_a'`，`Env` 由 `rfl`。

**(2′) ✅ (G-a) 本轮当场关掉（lane-leafa-gen，`RecVJFromParts.lean`，已进 build）。**
`Nivat.LaneLeafAGenRecVJ.rec_vJ_of_parts`（`RecVJFromParts.lean:106`）**只吃 `c` 一个参数**
就给出第 25 条，`toChainDataGeom_of_parts`（`:115`）随即由 24 个字段造出 `ChainDataGeom`。
全量 build 实测公理全白：`[propext, Classical.choice, Quot.sound]`（三条都是）。
⟹ 上面 (1) 那条「死路」只说对了一半：`IsLatticeConvexRegion` **单独**确实推不出 `rec_vJ`
（有界集反例成立，不撤回），但 `Nivat.Colle35.rec_vJ_of_bottom`（`ItemII.lean:766`）把它
**配上另外五条**就够，而那五条逐条都是本结构体的字段：`c.hsweep` / `c.hhp` / `c.hswept` /
`c.F.dot_nJ_vJ` / `c.bottom`。当年在 `ofParts` 上接不通的真原因是
**`ofParts` 的 `Env` 是自由变量**（`ChainExhaust.lean:27-31` 逐字记着），
而 `ChainDataGeomParts` 的 `maxA`（`ChainPartsFeed.lean:190`）把 `EnvOf (↑S)` 写死了
⟹ 取 `hEnv := rfl`，那道障碍在这张表上根本不存在。缺的从来不是数学，是接线。
⟹ **洞 1 的残余现在是两条：(G-b) 与 (G-c)。**

**(3) ⚠ 读法限定（§15）。** 本条 (2) 是**读法**，不是内核事实：没有任何
`ChainDataGeomParts` 在树中被填出来过，(G-a)(G-b)(G-c) 三条也没有一条被形式化地证明为
「恰好只欠这三条」。本段的作用是把靶子命名到字段级，硬规矩 1 的闸门不因此移动。 -/

/-! ### The four leaves of `region_case1`

`region_case1` below is **pure assembly**: its body contains no `sorry`, and every hole in it
is one of the four theorems in this block.  The decomposition was validated before it was
landed — `tmp/case1_skeleton.lean` states these four signatures with `sorry` bodies, restates
`region_case1` verbatim, and derives it by the same assembly; that file compiles with `RC=0`
under `set_option autoImplicit false`, with `sorry` warnings on exactly the four leaves and
none on the assembly (2026-09-17).

The split follows the `region_case1` docstring below, i.e. Collé `b3_colle2.txt:780-862`:

| leaf | paper | content |
|---|---|---|
| `case1_claim46_and_selection` | Claim 4.6 `:780-804` + `I`/`N` selection `:806-820` | Lemma 4.1's data bundle |
| `case1_claim47_semiAmbiguous` | Claim 4.7 `:822-852` | `hamb` |
| `case1_sweep`                 | `Lemma41.lean:776-779` | `hsweep` |

The assembly step itself is `Nivat.Colle41.lemma41_colle_region_shape` (`Lemma41.lean:767`),
which is already `sorry`-free.

⚠ Landing this raises the `sorry` count in this file from one to four while leaving
`axiom_closure` unchanged.  That is the intended trade: the `sorry`s now sit on named
mathematical statements with paper line numbers instead of on an undivided 80-line obligation.
Per `CLAUDE.md`, progress is measured by `axiom_closure`, not by `sorry` count. -/

/-! ═══ 以下整块由集成者于 2026-09-20 从文件末尾上移到此处 ═══

**为什么必须上移**：Lean 要求声明先于使用。`wedgeResidualR_of_case1_of_cone_at_base_of_agree`
原先在 `:3314`，而它要填的 `exists_wedgeResidualR` 的洞在 `:1213`——**装配器在洞的下游，
在同一个文件里，永远不可能被那个洞调用**。这不是数学问题，是文件拓扑问题，
而它在「接链」这件事上是完全隐形的：`check1.sh` EXIT=0、`lake build` rc=0、
`#print axioms` 干净、`onchain.py` 也算它在链上——每一项实测都是绿的，
而这条引理对它声称要填的洞**在结构上不可用**。

实测依据：本块（原 `:2772`–`:3373`，602 行）对 `:1286`–`:2771` 区间内定义的 23 个声明
**一个都不引用**，所以整块上移是安全的（逐名扫描，非目测）。 -/

/-! ## L1 接链：`exists_wedgeResidualR` 的锥/半带路线（2026-09-20）

`CLAUDE.md` 硬规矩 9 要求一条引理的**消费者**在落地的同一轮被点名。本节就是那个动作的
L1 侧：把两条链外但 "UP" 的生产者接到 `exists_wedgeResidualR`（`:1195` 的 `sorry`）上。 -/

/-- **`exists_wedgeResidualR` 的结论，从锥几何 + `hmono` 直接产出**（接链，2026-09-20）。

这是 `StrictWindow.hbase_of_cone_halfStrip_of_hmono`（`StrictWindow.lean:1037`）与
`WedgeAssemble.nonempty_wedgeResidualR_of_hbase_at_shear`（`WedgeAssemble.lean:81`）的合成，
两条生产者在本次 import 之前都不在主定理的可达闭包里。

**消费者**：本文件 `exists_wedgeResidualR`（`:1132`，洞在 `:1195`）的结论
`Nonempty (L1Claim.WedgeResidualR ξ S vl)` 与本定理的结论**逐字相同**，所以关掉那个洞只差
把下面的前提在该定理的 binder 下兑现，不再需要任何新的中间命题。

**剪切不是 `∀ K`**（硬规矩 7）：`K` 是显式参数，锥侧的三条前提 `hstep`/`hcone`/`hstrip`
与 `hmono`、`hchain` 全部只在**这一个** `u' - K • vl` 上陈述；`WedgeAssemble` 那侧的
`hcorner` 也在同一个剪切上。`K`、`a`、`hcorner` 可由
`WedgeAssemble.exists_shear_corner_data`（`:109`）从 `d.Sphi.Nonempty` 无条件产出，
所以调用方真正要兑现的只有几何前提。

**两条具名的债（不是本定理的缺陷，是它如实暴露的）**：
* `hchain`：`chainFull` 沿 `±vl` 双向扫，`coneRegion` 只扫 `+vl`；
  `Nivat.ConeHbase.not_chainFull_subset_coneRegion` 是这个包含在一般情形下为假的内核见证。
* `hmono`：`EnvFit.not_exists_shear_hmono`（`EnvFit.lean:918`）证明**没有加 envelopedness 时**
  不存在剪切使 `hmono` 成立（见证 `Bgap` 的最低层面是一个**顶点**而不是边，故
  `(0,-1) ∉ E Bgap`，被 Definition 3.2 与 `b3_colle2.txt:774` 排除——与 `leanTri` 同型）。
  所以 `hmono` 的正确出口是 envelopedness 下的 occupancy 引理，不是换个剪切。

原文：b3_colle2.txt:792-804（Figure 10 的放置归纳）与 `:774`（`𝒮` 有平行于 `ℓ` 与 `-ℓ` 的边）。 -/
theorem wedgeResidualR_of_cone_hmono_at_shear
    {e : ℤ × ℤ} (hξ : IsMinimalCounterexample ξ) (d : DecompDataZ ξ)
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S) (hS : S.Nonempty)
    {Sw : Finset (ℤ × ℤ)} {a₀ : ℤ × ℤ}
    {B : Set (ℤ × ℤ)} {u' b₀ nℓ : ℤ × ℤ} {c cz : ℤ}
    -- 🔴 2026-09-21 集成者：`GeneratesAt ξ Sw a₀` 换成原文 `:786`+`:790`+`:792` 的捆绑形状。
    -- 原文从未断言 `𝒮_{φ_ι}` 生成 `ξ` 本身，只断言它在 `ZMod p` 里生成差 `η − η̄_{ι₀}`。
    (hSwgen : Nivat.SweepLines.ReducedGeneratesAt ξ Sw a₀ (c • vl))
    (ha₀ : a₀ ∈ Sw) (hconv : Nivat.LatticeConvex (Sw.erase a₀))
    (hb₀ : b₀ ∈ B) (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hc : 0 < c) (hvl_prim : Primitive vl) (K : ℤ) (k : ℕ)
    (hD : ∀ z ∈ Nivat.LE2.halfStrip B vl, (T e ξ) z = T (c • vl) (T e ξ) z)
    (hperp : Nivat.LE2.dot nℓ vl = 0)
    (hstep : Nivat.LE2.dot nℓ (u' - K • vl) = -1)
    (hstrict : ∀ z ∈ Sw.erase a₀, Nivat.LE2.dot nℓ a₀ < Nivat.LE2.dot nℓ z)
    (hcone : ∀ w ∈ Nivat.ConeRegion.coneRegion B vl (u' - K • vl),
      Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ Sw.erase a₀, Nivat.LE2.dot nℓ (z + (w - a₀)) < cz →
        z + (w - a₀) ∈ Nivat.ConeRegion.coneRegion B vl (u' - K • vl))
    (hstrip : ∀ w ∈ Nivat.ConeRegion.coneRegion B vl (u' - K • vl),
      Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ Sw.erase a₀, cz ≤ Nivat.LE2.dot nℓ (z + (w - a₀)) →
        z + (w - a₀) ∈ Nivat.LE2.halfStrip B vl)
    (hmono : ∀ b ∈ B, ∀ t : ℕ, cz ≤ Nivat.LE2.dot nℓ b - (t : ℤ) →
      b + (t : ℤ) • (u' - K • vl) ∈ Nivat.LE2.halfStrip B vl)
    (hchain : chainFull B vl (u' - K • vl) b₀ k ⊆
      Nivat.ConeRegion.coneRegion B vl (u' - K • vl))
    {a : ℤ × ℤ} (ha : a ∈ d.toDecompData.Sphi)
    (hcorner : ∀ b ∈ d.toDecompData.Sphi,
      0 ≤ Nivat.LE2.dot (expNormal (u' - K • vl) vl) (b - a) ∧
        0 ≤ Nivat.L1Line0.uCoord (u' - K • vl) vl a b) :
    Nonempty (L1Claim.WedgeResidualR ξ S vl) :=
  Nivat.WedgeAssemble.nonempty_wedgeResidualR_of_hbase_at_shear hξ d hb₀ hunimod hc hvl_prim K k
    (Nivat.StrictWindow.hbase_of_cone_halfStrip_of_hmono hSwgen ha₀ hconv k hD hperp hstep
      hstrict hcone hstrip hmono hchain) ha hcorner hS

/-- **阶段一的输出单独成条**（两阶段拆分第一步，2026-09-20，用户裁决「按原文拆成两阶段」）。

原文：b3_colle2.txt:780-804（Claim 4.6）。**Claim 4.6 的结论只有周期性**——
`(T^u η)|𝓡_{ι−1}` 以平行 `ℓ` 的向量为周期——**它一个字都没提角点**。
角点 `a`（`hcorner`）属于 Figure 11(B)（`:848-856`），那是第二阶段 `𝓡^n_I` 的扫掠，
方向对是 `(ℓ' = ℓ_I, v⃗_{ℓ_{I−1}})`，与本条的 `(ℓ, v⃗_{ℓ_{ι−1}})` **不是同一对**。

**为什么必须拆**（内核事实，不是读法）：`CornerAdjClash.det_eq_zero_of_adj_of_corner`
证明 `hadj ∧ hcorner` 在**同一个** `(vl, u')` 上迫使 `𝒮_φ` 所有 `vl`-坐标为负的边法向两两平行，
即 `m ≤ 2`；而剪切救不了——`hcorner` 对 `K` 上闭、`hmono` 对 `K` 下闭，只交于 `K = 0`。
所以本条**不带 `ha` / `hcorner`**：它是 Claim 4.6 逐字的形式化，只产 `hbase`。

结论里的 `b₀` 用存在量词而不是 binder：它由 `exists_argmax_base` 在有限非空 `B` 上无条件产出。 -/
theorem exists_hbase_of_cone_hmono_at_shear_of_argmax
    {e : ℤ × ℤ}
    {Sw : Finset (ℤ × ℤ)} {a₀ : ℤ × ℤ}
    {B : Set (ℤ × ℤ)} {u' nℓ : ℤ × ℤ} {c cz : ℤ}
    -- 🔴 2026-09-21 集成者：`GeneratesAt ξ Sw a₀` 换成原文 `:786`+`:790`+`:792` 的捆绑形状。
    -- 原文从未断言 `𝒮_{φ_ι}` 生成 `ξ` 本身，只断言它在 `ZMod p` 里生成差 `η − η̄_{ι₀}`。
    (hSwgen : Nivat.SweepLines.ReducedGeneratesAt ξ Sw a₀ (c • vl))
    (ha₀ : a₀ ∈ Sw) (hconv : Nivat.LatticeConvex (Sw.erase a₀))
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (K : ℤ) (k : ℕ)
    (hD : ∀ z ∈ Nivat.LE2.halfStrip (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl,
      (T e ξ) z = T (c • vl) (T e ξ) z)
    (hperp : Nivat.LE2.dot nℓ vl = 0)
    (hnu : Nivat.LE2.dot nℓ u' = -1)
    (hstrict : ∀ z ∈ Sw.erase a₀, Nivat.LE2.dot nℓ a₀ < Nivat.LE2.dot nℓ z)
    (hcone : ∀ w ∈ Nivat.ConeRegion.coneRegion (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl
        (u' - K • vl),
      Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ Sw.erase a₀, Nivat.LE2.dot nℓ (z + (w - a₀)) < cz →
        z + (w - a₀) ∈ Nivat.ConeRegion.coneRegion (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl
          (u' - K • vl))
    (hstrip : ∀ w ∈ Nivat.ConeRegion.coneRegion (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl
        (u' - K • vl),
      Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ Sw.erase a₀, cz ≤ Nivat.LE2.dot nℓ (z + (w - a₀)) →
        z + (w - a₀) ∈ Nivat.LE2.halfStrip (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl)
    (hmono : ∀ b ∈ Nivat.LE2.shift (-((k : ℤ) • vl)) B, ∀ t : ℕ,
      cz ≤ Nivat.LE2.dot nℓ b - (t : ℤ) →
        b + (t : ℤ) • (u' - K • vl) ∈
          Nivat.LE2.halfStrip (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl) :
    ∃ b₀ ∈ B, Nivat.Colle41.PeriodOn (T e ξ)
      (Nivat.ColleReg.chainFull B vl (u' - K • vl) b₀ k) (c • vl) := by
  obtain ⟨b₀, hb₀, hb₀max⟩ :=
    Nivat.StrictWindow.exists_argmax_base hBfin hBne (u' - K • vl) vl
  have hunimod' : det (u' - K • vl) vl = 1 ∨ det (u' - K • vl) vl = -1 := by
    rwa [Nivat.L1StraddleWedge.det_shear]
  have hstep' : Nivat.LE2.dot nℓ (u' - K • vl) = -1 := by
    have hexp : Nivat.LE2.dot nℓ (u' - K • vl)
        = Nivat.LE2.dot nℓ u' - K * Nivat.LE2.dot nℓ vl := by
      simp only [Nivat.LE2.dot, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul]
      ring
    rw [hexp, hperp, hnu]; ring
  exact ⟨b₀, hb₀,
    Nivat.StrictWindow.hbase_of_cone_halfStrip_of_hmono_of_argmax hSwgen ha₀ hconv k hunimod'
      hb₀max hD hperp hstep' hstrict hcone hstrip hmono⟩

/-- **Claim 4.6 逐字**（两阶段拆分，阶段一的**原文形**，2026-09-20）。

原文：b3_colle2.txt:780-804。`:804` 的结论一字不差是

> `(T^u η)|_{𝓡_{ι−1}}` is periodic with period parallel to `ℓ`.

链上词典（`NOTATION.md`）：`𝓡_{ι−1} = Nivat.ConeRegion.coneRegion B vl u'`
（`= B + ℕvl + ℕu'`，`:780` 的 `H_B(ℓ) + ℕ v⃗_{ℓ_{ι−1}}`）、`H_B(ℓ) = Nivat.LE2.halfStrip B vl`
（Definition 3.4，`:412-414`）、「period parallel to `ℓ`」`= c • vl`。

## 逐量词对应（硬规矩 7）

| 本条 | 原文 | 说明 |
|---|---|---|
| `Sw`、`ha₀`、`hconv` | `:792` `𝒮_{φ_ι}` 与其 `nℓ`-极小点 | Lemma 2.5 的生成集 |
| `hstrict` | `:792` Lemma 2.6「无平行 `±ℓ` 的边」 | 极小面是单点 |
| `hD` | `:798` `(T^u η)|_{H_B(ℓ)}` 已有周期 `h` | 扫掠的种子 |
| `lines i` | `:794-796` `l₁ := ℓ_B^{(−)}`、`l₂ := l₁^{(−)}`… | 平行 `ℓ` 的一族直线，逐条推进 |
| `hcone`/`hstrip` | `:796` 窗口其余点落在 `H_B(ℓ) ∪ A₁ ∪ ⋯ ∪ A_{k−1}` | 两个落点分支 |
| `hmono` | `:774`＋`:777` enveloped ⟹ 占据性 | `𝓡_{ι−1}` 被种子与直线族穷尽 |

## 本条**没有**什么（这是拆分的全部意义）

**没有角点 `hcorner`、没有剪切 `K`、没有 `k`、没有 argmax `b₀`。** 那四样都属于第二阶段
（`:806-856`，Figure 11(B)）。`CornerAdjClash.det_eq_zero_of_adj_of_corner` 是内核见证：
`hadj ∧ hcorner` 绑在同一个 `(vl, u')` 上迫使 `m ≤ 2`。所以阶段一必须以 `coneRegion` 上的
周期性收尾，不能顺手把角点框也带上。

结论比 `exists_hbase_of_cone_hmono_at_shear_of_argmax` **严格强**：那条给的是
`chainFull B vl (u' - K•vl) b₀ k` 上的周期性（`chainFull` 是 `wedgeFull` 的一个截，
沿 `±vl` 扫），本条给的是整个 `𝓡_{ι−1}` 上的周期性，且不需要 `chainFull ⊆ coneRegion`
（`ConeHbase.not_chainFull_subset_coneRegion` 证明该包含一般为假）。 -/
theorem claim46_periodOn_coneRegion
    {e : ℤ × ℤ}
    {Sw : Finset (ℤ × ℤ)} {a₀ : ℤ × ℤ}
    {B : Set (ℤ × ℤ)} {u' nℓ : ℤ × ℤ} {c cz : ℤ}
    -- 🔴 2026-09-21 集成者：`GeneratesAt ξ Sw a₀` 换成原文 `:786`+`:790`+`:792` 的捆绑形状。
    -- 原文从未断言 `𝒮_{φ_ι}` 生成 `ξ` 本身，只断言它在 `ZMod p` 里生成差 `η − η̄_{ι₀}`。
    (hSwgen : Nivat.SweepLines.ReducedGeneratesAt ξ Sw a₀ (c • vl))
    (ha₀ : a₀ ∈ Sw) (hconv : Nivat.LatticeConvex (Sw.erase a₀))
    (hD : ∀ z ∈ Nivat.LE2.halfStrip B vl, (T e ξ) z = T (c • vl) (T e ξ) z)
    (hperp : Nivat.LE2.dot nℓ vl = 0)
    (hnu : Nivat.LE2.dot nℓ u' = -1)
    (hstrict : ∀ z ∈ Sw.erase a₀, Nivat.LE2.dot nℓ a₀ < Nivat.LE2.dot nℓ z)
    (hcone : ∀ w ∈ Nivat.ConeRegion.coneRegion B vl u',
      Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ Sw.erase a₀, Nivat.LE2.dot nℓ (z + (w - a₀)) < cz →
        z + (w - a₀) ∈ Nivat.ConeRegion.coneRegion B vl u')
    (hstrip : ∀ w ∈ Nivat.ConeRegion.coneRegion B vl u',
      Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ Sw.erase a₀, cz ≤ Nivat.LE2.dot nℓ (z + (w - a₀)) →
        z + (w - a₀) ∈ Nivat.LE2.halfStrip B vl)
    (hmono : ∀ b ∈ B, ∀ t : ℕ, cz ≤ Nivat.LE2.dot nℓ b - (t : ℤ) →
      b + (t : ℤ) • u' ∈ Nivat.LE2.halfStrip B vl) :
    Nivat.Colle41.PeriodOn (T e ξ) (Nivat.ConeRegion.coneRegion B vl u') (c • vl) :=
  Nivat.SweepLines.hbase_at_of_reducedGeneratesAt hSwgen hD
    (fun i => Nivat.ConeRegion.coneRegion B vl u' ∩
      {y | Nivat.LE2.dot nℓ y = cz - 1 - (i : ℤ)})
    (Nivat.StrictWindow.hwinL_cone_halfStrip_of_hstrict_of_geom hstrict hcone hstrip)
    (Nivat.StrictWindow.coneRegion_subset_halfStrip_union_lines_of_hmono hperp hnu hmono)

/-- **Claim 4.6 在 Case 1 形态下的完整出口**（两阶段拆分，阶段一接链，2026-09-20）。

原文：b3_colle2.txt:758（Case 1）、`:774`（两条边）、`:777`（enveloped）、`:778`（`hu`）、
`:780-804`（Claim 4.6 本体）。

与 `claim46_periodOn_coneRegion` 结论同型，但 **`hmono`、`hD`、`c` 三条全部就地打掉**，
兑现物与 `wedgeResidualR_of_case1_of_cone_at_base_of_agree` 逐条相同：

* `hmono` ← `EnvFit.hmono_of_adjacent_of_enveloped`（`EnvFit.lean:2404`），`K = 0`；
  它要的 `hESfin` / `hEbot` / `hEtop` 分别由 `finite_E_of_finite`、
  `neg_mem_E_Sphi_of_dot_eq_zero`、`mem_E_Sphi_of_dot_eq_zero` 白给。
* `c` ← `L1Line0.exists_pos_zsmul_mem_Per hvl_prim hp_mem hp_ne hdet_vl`（`p ∈ Per xper`、
  `p ∦ 0`、`p ⊥ nℓ` ⟹ `vl` 的某个正倍数是 `xper` 的周期）。
* `hD` ← `L1Line0.hD_of_agree_halfStrip hu hc.le hper`（`:778` 的 `T^u η ≡ x_per` 在 `H_B(ℓ)` 上）。

**剩下的几何债只有 `hcone` / `hstrip` 两条**（外加洞 3 的 `hSwgen` 占位）——
这正是 `:796` 的两个落点分支。**没有 `hcorner`、没有剪切、没有 `k`。** -/
theorem claim46_of_case1
    {e : ℤ × ℤ} (d : DecompDataZ ξ)
    {Sw : Finset (ℤ × ℤ)} {a₀ : ℤ × ℤ}
    -- 🔴 2026-09-21 集成者：`GeneratesAt ξ Sw a₀` 换成原文 `:786`+`:790`+`:792` 的捆绑形状。
    -- 这里 `c` **不是 binder**（它由 `exists_pos_zsmul_mem_Per` 在体内产出），所以用的是
    -- `:790` 逐字的**方向**形 `ReducedGeneratesAtDir`：「`η̄_{ι₀}` 有某个平行于 `ℓ` 的周期」。
    -- 体内用 `reducedGeneratesAt_of_dir` 过到公倍数 `c * c₀` 上。
    (hSwgen : Nivat.SweepLines.ReducedGeneratesAtDir ξ Sw a₀ vl)
    (ha₀ : a₀ ∈ Sw) (hconv : Nivat.LatticeConvex (Sw.erase a₀))
    {B : Set (ℤ × ℤ)} {u' nℓ : ℤ × ℤ} {cz : ℤ}
    (henv : Nivat.LE2.EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) B)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hvl_prim : Primitive vl)
    (hu : ∀ z ∈ Nivat.LE2.halfStrip B vl, T e ξ z = xper z)
    (hp_mem : p ∈ Per xper) (hp_ne : p ≠ 0) (hdet_vl : det p vl = 0)
    (hperp : Nivat.LE2.dot nℓ vl = 0)
    (hnu : Nivat.LE2.dot nℓ u' = -1)
    (hstrict : ∀ z ∈ Sw.erase a₀, Nivat.LE2.dot nℓ a₀ < Nivat.LE2.dot nℓ z)
    (hprim : Nivat.LE2.Prim nℓ) (i : Fin d.toDecompData.m)
    (hdoth : Nivat.LE2.dot nℓ (d.toDecompData.h i) = 0)
    (hcz : ∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b)
    (hczmem : ∃ b ∈ B, Nivat.LE2.dot nℓ b = cz)
    (hadj : ∀ n ∈ Nivat.LE2.E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)),
      ¬ (Nivat.LE2.dot n vl < 0 ∧ 0 < Nivat.LE2.dot n u'))
    (hcone : ∀ w ∈ Nivat.ConeRegion.coneRegion B vl u',
      Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ Sw.erase a₀, Nivat.LE2.dot nℓ (z + (w - a₀)) < cz →
        z + (w - a₀) ∈ Nivat.ConeRegion.coneRegion B vl u')
    (hstrip : ∀ w ∈ Nivat.ConeRegion.coneRegion B vl u',
      Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ Sw.erase a₀, cz ≤ Nivat.LE2.dot nℓ (z + (w - a₀)) →
        z + (w - a₀) ∈ Nivat.LE2.halfStrip B vl) :
    ∃ c : ℤ, 0 < c ∧
      Nivat.Colle41.PeriodOn (T e ξ) (Nivat.ConeRegion.coneRegion B vl u') (c • vl) := by
  obtain ⟨c, hc, hper⟩ :=
    Nivat.L1Line0.exists_pos_zsmul_mem_Per hvl_prim hp_mem hp_ne hdet_vl
  obtain ⟨c₀, hc₀, hR⟩ := Nivat.SweepLines.reducedGeneratesAt_of_dir hSwgen
  have hper' : (c * c₀) • vl ∈ Per xper := by
    have : (c * c₀) • vl = c₀ • (c • vl) := by rw [mul_comm, mul_smul]
    rw [this]
    exact AddSubgroup.zsmul_mem _ hper c₀
  refine ⟨c * c₀, mul_pos hc hc₀, claim46_periodOn_coneRegion (hR c) ha₀ hconv
    (Nivat.L1Line0.hD_of_agree_halfStrip hu (mul_pos hc hc₀).le hper')
    hperp hnu hstrict hcone hstrip ?_⟩
  exact Nivat.EnvFit.hmono_of_adjacent_of_enveloped hunimod
    (Nivat.LE2.finite_E_of_finite (d.toDecompData.Sphi.finite_toSet))
    (Nivat.LE2.envOf_iff.mp henv) hBfin hBne hperp hnu
    (d.toDecompData.neg_mem_E_Sphi_of_dot_eq_zero hprim i hdoth)
    (d.toDecompData.mem_E_Sphi_of_dot_eq_zero hprim i hdoth)
    hcz hczmem hadj

/-- **换框步里可证的那一半：接线**（2026-09-20，集成者之手，**无 `sorry`**）。

原文：b3_colle2.txt:806-818。`exists_stage2_frame_of_claim46`（**2026-09-21 已退役**，
逐字副本在 `tmp/wip/Stage2FrameRetired.lean`；理由见 `OPEN.md #21`）的结论是个五元存在，
本条说明其中**四元加两条性质是纯接线**：取 `R := B`、`u₂ := u' - K • vl`、`k := 0`，
`PeriodOn` 在集合上反变（`Colle41.PeriodOn.mono`，`Lemma41.lean:662`），所以阶段一给的
`coneRegion` 上的周期性只要被 `hsub` 包住就直接落到 `chainFull` 上。

**剪切不改 `wedgeFull`**：`B + ℤvl + ℕ(u' - K•vl) = B + ℤvl + ℕu'`（`ℤvl` 吸收掉 `-tK•vl`），
变的只有切割法向 `expNormal (u' - K•vl) vl`，这正是 `:818` 的 `𝓡^n_I` 换成 `v⃗_{ℓ_{I−1}}`
之后发生的事。

**留给 `hsub` 的是什么**：`Nivat.ConeHbase.not_chainFull_subset_coneRegion`
（`ConeHbase.lean:208`）已证**无条件**的 `chainFull ⊆ coneRegion` 为假，所以 `hsub`
不能凭空得到；它要的两个前提是 (i) `b₀` 是 `expNormal (u' - K•vl) vl`-极大点、
(ii) `K ≤ 0`。这两条连同 `ha`/`hcorner` 一起是 `exists_stage2_frame_of_claim46`
仅剩的那个 `sorry`。 -/
theorem stage2_frame_of_shear_corner
    {e : ℤ × ℤ} (d : DecompDataZ ξ)
    {B : Set (ℤ × ℤ)} {u' b₀ : ℤ × ℤ} {K c : ℤ}
    (hb₀ : b₀ ∈ B)
    (hunimod₂ : det (u' - K • vl) vl = 1 ∨ det (u' - K • vl) vl = -1)
    (hsub : Nivat.ColleReg.chainFull B vl (u' - K • vl) b₀ 0 ⊆
      Nivat.ConeRegion.coneRegion B vl u')
    (hbase₁ : Nivat.Colle41.PeriodOn (T e ξ)
      (Nivat.ConeRegion.coneRegion B vl u') (c • vl))
    {a : ℤ × ℤ} (ha : a ∈ d.toDecompData.Sphi)
    (hcorner : ∀ b ∈ d.toDecompData.Sphi,
      0 ≤ Nivat.LE2.dot (expNormal (u' - K • vl) vl) (b - a) ∧
        0 ≤ Nivat.L1Line0.uCoord (u' - K • vl) vl a b) :
    ∃ (R : Set (ℤ × ℤ)) (u₂ b₀ : ℤ × ℤ) (k : ℕ),
      (det u₂ vl = 1 ∨ det u₂ vl = -1) ∧ b₀ ∈ R ∧
      Nivat.Colle41.PeriodOn (T e ξ)
        (Nivat.ColleReg.chainFull R vl u₂ b₀ k) (c • vl) ∧
      ∃ a ∈ d.toDecompData.Sphi, ∀ b ∈ d.toDecompData.Sphi,
        0 ≤ Nivat.LE2.dot (expNormal u₂ vl) (b - a) ∧
          0 ≤ Nivat.L1Line0.uCoord u₂ vl a b :=
  ⟨B, u' - K • vl, b₀, 0, hunimod₂, hb₀,
    Nivat.Colle41.PeriodOn.mono hsub hbase₁, a, ha, hcorner⟩

/- **阶段一 → 阶段二的换框步**（2026-09-21 改框，集成者之手，`OPEN.md #21`）。

原文：b3_colle2.txt:806-856。**这是本次拆分留下的唯一新债**，且它就是原文这一整段的内容。

## 🔴 2026-09-21：上一版 `exists_stage2_frame_of_claim46` 已退役

上一版的结论是 `∃ R u₂ b₀ k, … PeriodOn (chainFull R vl u₂ b₀ k) (c•vl) ∧ ha ∧ hcorner`，
逐字副本在 `tmp/wip/Stage2FrameRetired.lean`（**在 `tmp/`，未落地**，带 `sorry`）。
退役理由是**生长方向**（三条独立证据见 `OPEN.md #21`，其中最干净的一条）：

`chainFull B vl u' b₀ k = wedgeFull B vl u' ∩ {z | lev k ≤ dot (expNormal u' vl) z}`
的切割线平行 `u'`、层数沿 `vl` 计，所以 `k` 增大暴露的是 **`-vl` 方向**的新层；
而 `:818` 的 `𝓡^n_I := {g + t·v⃗_{ℓ_{I−1}} : g ∈ 𝓡_I, dist(·, ℓ'_{𝓡_I}) ≤ d_n}`
切割线平行 `ℓ' = ℓ_I`、沿 **`v⃗_{ℓ_{I−1}}`** 生长。按字典「我们的 `u'` ↔ 原文 `v⃗_{ℓ_I}`、
我们的 `-vl` ↔ 原文 `v⃗_{ℓ_{I−1}}`」两者重合当且仅当 `I = ι−m+1`（塔顶，`:812`），
而 `:814` 取的是**最小**的 `I`，一般不在塔顶。所以旧结论在 `m ≥ 3`、`I > ι−m+1` 时
**比 `:806-856` 强**（硬规矩 7：比原文强 = 债；被反例打中也不产生关于原文的信息）。

## 逐量词对应（硬规矩 7）

结论 `Nonempty (L1Claim.CutResidualR ξ S vl)` 的每个字段都在
`L1Claim.CutResidualR`（`L1Claim.lean` §5）的 docstring 里逐条标了原文行号：
`Rinf = 𝓡_{I−1}`（`:808`）、`u' = v⃗_{ℓ_I}`（`:816`）、`lev = -d_n`（`:816`，**已达到**的
距离）、`hbase` = `𝓡^0_I = 𝓡_I` 周期（`:814`，`I` 的定义性质）、`hinf` = `I` 极小
（`:814`）、`hline`/`hcover` = Claim 4.7 与 Figure 11(B)（`:824`、`:848-856`）。

`hξ` 进签名是因为 `:810` 要 Proposition 2.12（`(T^u η)|𝓗(ℓ_{ι−m})` 没有平行 `ℓ_{ι−m}`
或 `ℓ` 的周期），那是关于极小反例的陈述；`d` 进签名是因为 `I` 的取值范围由 `𝒮_φ` 的
边方向枚举（`:764`）给出；`hgen` 付 `CutResidualR.hgen`（Figure 11(B) 的覆盖要一个生成集）。

## 换框买到了什么（都不是新数学，是删掉我们自己加的量词）

* **`hunimod` 不再进结论。** `u' := v⃗_{ℓ_I}` 只需 `Primitive`（边方向）＋ `det vl u' ≠ 0`
  （`ℓ_I ≠ ℓ`，因 `I ≤ ι−1`）。`det u₂ vl = ±1` 是 `chainFull` 作为象限的编码产物，
  原文从未对 `(vl, v⃗_{ℓ_I})` 断言幺模。
* **角点子句 `hcorner` 整项消失。** Claim 4.7（`:824`）给的是**放置**
  `𝒯 ∖ ℓ'_𝒯 ⊂ 𝓡^N_I`、`𝒯 ⊄ 𝓡^N_I`，不是角点。`CornerAdjClash.det_eq_zero_of_adj_of_corner`
  （内核事实）杀的是阶段一框里的角点，本框从来不适用。
* **`:806-820` 的塔不必是 `RegionFamily`。** 原文的外层塔是**有限**的
  （`:806`，`ι−m+1 ≤ i ≤ ι−2`，共 `m−1` 项），所以它只需要「有限多个里取最小 `I`」，
  `RegionFamily` 只用在**内层** `𝓡^n_I`（`:818`，`n` 无界），而内层恰好就是
  `Nivat.L1Region.ofCut`（`L1Region.lean:240`）——一条写好了、内核干净、**至今没有生产者**
  的半平面切割装配器。

## 债的形状（派工用）

`CutResidualR` 有 11 项数据 ＋ 12 条证明义务，**每条都能单独派**。按原文分三组：

0. **`hlev` / `hexh` / `hgap`（`:816`）已由 `Nivat.CutLevels.exists_lev_for_ofCut`
   （`CutLevels.lean:97`，2026-09-21 落地，`#print axioms` 干净）归约掉。** 生产者现在只欠
   **两条**：`∃ z ∈ Rinf, dot m z = b₀`（`d₀ = 0` 那一层被取到）与
   `∀ b, ∃ z ∈ Rinf, dot m z < b`（`𝓡_{I−1}` 含 `v⃗_{ℓ_{I−1}}` 射线，故离 `ℓ'` 任意远）。
   `lev 0 = b₀` 也在那条引理的结论里，用来把 `cut Rinf m lev 0` 认成 `𝓡^0_I`。
   那两条里的第二条也已归约：`Nivat.CutLevels.exists_lev_for_ofCut_of_ray`
   （`CutLevels.lean:145`）把它换成原文 `:806` 直接给的那条 `v⃗_{ℓ_{I−1}}` 射线
   （`∀ k : ℕ, z₀ + k•w ∈ Rinf` ＋ `dot m w < 0`）。⚠ 该射线**推不出**
   `Colle41.IsRegion Rinf vl u'`：后者的两条射线一条升层（`hmu`）、一条平层（`hmu'`），
   都不降层；降层射线是**塔的构造**给的，不是 region 谓词给的。
1. **`hR` / `hmu'` / `hmu`**（`:808`、`:818`）：`𝓡_{I−1}` 是 `(−ℓ, ℓ_{I−1})`-region
   （Def 3.1，`:386`），切割法向垂直 `ℓ'`。这一组是几何，与 `ξ` 无关。
   🔴 **2026-09-21：`hR` 的上游断言（`:806` 说每级 `𝓡_i` 都是 region）按 `:31` 一般为假**，
   两个内核反例：`Colle41.not_isLatticeConvexRegion_sweep_quadrant`（`SweepNotRegion.lean:194`，
   象限沿 `(2,−3)`）与 `SweepEdge.not_isLatticeConvexRegion_swept`（`SweepEdgeFail.lean`，
   三角形沿**自己的边方向** `(1,0)`，`(7,13)` 在凸包里不在集合里）。后者打掉了
   「扫掠方向平行于一条边」这条最像原文的补法。归约已落地：
   `Nivat.SweepCrit.isLatticeConvexRegion_halfStrip_of_chord`（`SweepCriterion.lean`）把整条
   断言换成唯一一条弦义务 `hchord`（格点能沿 `−v` 退回整数步），
   `Nivat.SweepCrit.chord_of_unit_backstep` 再把 `hchord` 换成「弦长 ≥ 1」。
   **未形式化的那一步**：弦长沿横向是凹函数，故两端层上各有一条 `v`-平行边（`𝒮_φ` 是
   zonotope，边成 `±` 对；Def 3.2 `:402` 的 `|E(T)| = |E(𝒰)|` 给出双侧）即可顶到 ≥ 1。
   反例的三角形只有**一条** `(1,0)`-平行边，所以它不 enveloped，打不到原文（硬规矩 10）。
2. **`hbase` / `hinf`**（`:814`）：`I` 的极小性。**指标选取那一步已由
   `Nivat.TowerIndex.exists_last_periodOn_finite`（`TowerIndex.lean:46`，2026-09-21 落地，
   `#print axioms` 干净）归约掉**——生产者只欠塔的**两端**：塔底 `R 0` 周期
   （`:806`，就是本签名的输入 `hbase₁`，经 `PeriodOn.mono` 落到 `coneRegion` 上）与
   塔顶 `R M` 不周期（`:810` 的 Proposition 2.12，带 `hξ` 的那一步）。
   中间的「逐级 `ℕ` 扫上去取最小的仍周期者」不必再写。`hbase` 由
   `TowerIndex.periodOn_of_le_last`（`:75`）／`PeriodOn.mono` 从 `R I` 落到
   `cut Rinf m lev 0`；`hinf` 就是 `R (I+1)` 的不周期性。
   ⚠ 真正的欠债是**塔本身**：`R : ℕ → Set (ℤ×ℤ)` 要按 `:806` 的
   `𝓡_i := {g + t·v⃗_{ℓ_i} : g ∈ 𝓡_{i+1}, t ∈ ℤ₊}` 造出来，且每级仍是 region。
   ⚠ 「每级仍是 region」正是上面第 1 组新增的那条——**它不是定义白拿的**，
   每一级都要兑现一次 `Nivat.SweepCrit.isLatticeConvexRegion_halfStrip_of_chord` 的 `hchord`。
3. **`hline` / `hcover`**（`:824`、`:848-856`）：Claim 4.7 的放置与 Figure 11(B) 的覆盖。
   🟢 **2026-09-21：`hline` 的放置部分已归约。**
   `Nivat.L1Claim.exists_tau_mem_cut_pair`（`WindowPlace.lean`，本轮落地并 import，
   `#print axioms` 干净）在
   `dot m u' = 0`、`0 < dot m vl`、`0 ≤ c`、`Q` 有限且整体位于 `≥ lev N` 层、
   ＋ **`htail`**（每个 `≥ lev N` 的层含一条 `u'`-尾在 `Rinf` 里）之下给出所需的 `τ`，
   且 `τ•u' + z` 与 `τ•u' + z + c•vl` 同时落进 `cut Rinf m lev N`。
   ⚠ **`hline` 的 `τ` 是 structure 字段（对所有 `N` 共用一个）**，而本引理的 `τ` 依赖 `N`——
   两者相容的理由是 `hline` 的两条前提（`N` 层周期、`N+1` 层不周期）**至多钉死一个 `N`**，
   该 `N` 由 `TowerIndex.exists_last_periodOn_finite` 给出，所以按它取 `τ` 即可。
   **剩余欠债只有 `htail`**：它是「`𝓡_{I−1}` 在每个 `≥ lev N` 的层上都含一条 `v⃗_{ℓ_I}`-尾」，
   正是下面那条原文理由的形式化。
   ⚠ 放置之所以办得到，是因为 `𝓡_{I−1}` 在每个 `≥ lev N` 的层上都含一条 `v⃗_{ℓ_I}`-尾
   （`𝓡_I` 含 `ℓ_I`-边射线 ＋ `ℕvl`，再 `+ℕ v⃗_{ℓ_{I−1}}`），取 `τ` 充分大即可。
   这条理由必须用上，不用就会像锥路线那样被单点集反例打中（硬规矩 10）。 -/

/-- **Assembly helper: construct `CutResidualR` from explicit pieces.**

Transforms the sorry below into documented field-level sorries.

Fields derived in body (6):
- `m`, `hmu'`, `hmu` (from `expNormal`)
- `det'`, `prim` (from `hunimod`)
- `c0` (from `hc`)

Fields from producers (4):
- `lev`, `hlev`, `hexh`, `hgap` — ⚠ **订正（第 199 轮，集成者实测调用点）：实际调用的是
  `CutLevels.exists_lev_consecutive`，不是初稿写的 `exists_lev_for_ofCut`。** 两者都存在
  （`CutLevels.lean` 的 `exists_lev_for_ofCut` / `exists_lev_consecutive`），后者在前者四条之外
  多给一条 `hconsec`（相邻两层之间无其它被取到的层），本证明体内 `obtain` 到的是**五**项不是四项。
  §57 甲类（引用指向存在但不是被调用的那条）。

Fields still needed as parameters (14):
- `v`, `τ`, `ε`, `Rinf`, `Sφ`, `a`, `hgen`, `hR`, `h0`, `hunb`, `hbase`, `hinf`, `hline`, `hcover`
-/
theorem exists_cutResidualR_of_claim46_ofPieces
    {e : ℤ × ℤ} (hξ : IsMinimalCounterexample ξ) (d : DecompDataZ ξ)
    (hgen_leaf : Nivat.Colle.GeneratesAt ξ S gen)
    {B : Set (ℤ × ℤ)} {u' nℓ : ℤ × ℤ} {c : ℤ}
    (henv : Nivat.LE2.EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) B)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hvl_prim : Primitive vl) (hc : 0 < c)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (hnu : Nivat.LE2.dot nℓ u' = -1)
    (hbase₁ : Nivat.Colle41.PeriodOn (T e ξ)
      (Nivat.ConeRegion.coneRegion B vl u') (c • vl))
    -- Data pieces (TODO: producers needed)
    (v : ℤ × ℤ)  -- window translation (Claim 4.7, b3_colle2.txt:824)
    (τ : ℤ)      -- placement parameter (`:826`, chosen after maximal index N)
    (ε : Bool)   -- which side is top face
    (Rinf : Set (ℤ × ℤ))  -- `𝓡_{I-1}`, the union of the tower (`:820`)
    -- 2026-09-22：阶段二的扫掠/切割方向是 `ℓ' = ℓ_I`（`:816`「we will write `ℓ_I = ℓ'`」，
    -- `:818` 的距离按 `ℓ'_{𝓡_I}` 量，`:826` 的放置沿 `v⃗_{ℓ'}`），它在指标 `I` 之后才定，
    -- **不是**阶段一的锥方向 `u'`（只有 `I = ι−1` 时两者重合）。`CutResidualR.u'`
    -- （`L1Claim.lean:1038`「runs along `ℓ' = ℓ_I`」）因此由 `w` 填，切割法向 `m ⟂ w`。
    -- 旧版把 `m := expNormal u' vl` 写死，lane-tower2 实测 `hbase`（`cut Rinf m lev 0 ⊆ 𝓡_I`）
    -- 在 `I < ι−1` 时不成立。
    (w : ℤ × ℤ) (hw_det : det vl w ≠ 0) (hw_prim : Primitive w)
    (m : ℤ × ℤ) (hmw : Nivat.LE2.dot m w = 0) (hmvl : 0 < Nivat.LE2.dot m vl)
    (Sφ : Finset (ℤ × ℤ)) (a : ℤ × ℤ)  -- generating set for Figure 11(B) (`:848-856`)
    -- Proof pieces (TODO: producers)
    (hgen : Nivat.Colle.GeneratesAt ξ Sφ a)  -- Figure 11(B) generator
    (hR : Colle41.IsRegion Rinf vl w)
    -- 距离序列（`:818` 的 `d_n`）。2026-09-22 改为显式 binder：原来在体内由 `h0`/`hunb` 经
    -- `CutLevels.exists_lev_for_ofCut` 产出，但 `hline`/`hcover` 的 `τ`/`v`/`ε` 在原文 `:826`
    -- 是**在 `N`（从而 `lev`）之后**选的（"there exists an integer `t₀ ∈ ℤ₊`"），
    -- `∃ τ, ∀ lev` 的量词序不可证（lane-l1-line 实测）。装配处先取 `lev` 再取 `τ`。
    (lev : ℕ → ℤ) (b₀ : ℤ)
    -- `b₀` 是 `:818` 的 `d_0 = 0` 所在的层（`ℓ'_{𝓡_I}` 支撑线的 `m`-高度），不是原点的层：
    -- 2026-09-22 lane-tower2 实测 `dot m 0` 版不可满足（`Rinf` 未必含原点所在层）。
    (hlev0 : lev 0 = b₀)
    (hlev : Antitone lev)
    (hexh : ∀ b : ℤ, ∃ n, lev n ≤ b)
    (hgap : ∀ n, ∃ z ∈ Rinf, lev (n + 1) ≤ Nivat.LE2.dot m z ∧ Nivat.LE2.dot m z < lev n)
    -- Periodicity (TODO: producers)
    (hbase : Nivat.Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev 0) (c • vl))
    (hinf : ¬ Nivat.Colle41.PeriodOn (T e ξ) Rinf (c • vl))
    -- Claim 4.7 placement (TODO: producer, see WindowPlace.lean per blueprint)
    (hline : ∀ (N : ℕ),
      Nivat.Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev N) (c • vl) →
      ¬ Nivat.Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev (N + 1)) (c • vl) →
      ∀ z ∈ L1Data.derivedQ ε w (S.image (· + v)),
        τ • w + z ∈ Nivat.L1Region.cut Rinf m lev N ∧
        τ • w + z + c • vl ∈ Nivat.L1Region.cut Rinf m lev N)
    -- Figure 11(B) cover (TODO: producer)
    (hcover : ∀ (N : ℕ),
      Nivat.Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev N) (c • vl) →
      ¬ Nivat.Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev (N + 1)) (c • vl) →
      ∀ g ∈ S.image (· + v), g ∉ L1Data.derivedQ ε w (S.image (· + v)) → ∀ t₀ : ℤ, τ ≤ t₀ →
        Nivat.L1StraddleMax.overlap (Nivat.L1Region.cut Rinf m lev (N + 1)) (c • vl) ⊆
          Nivat.MaxEnv.genClosure Sφ a
            (Nivat.L1StraddleMax.overlap (Nivat.L1Region.cut Rinf m lev N) (c • vl) ∪
              Nivat.L1StraddleMax.ray g w t₀))
    : Nonempty (L1Claim.CutResidualR ξ S vl) :=
  ⟨⟨e, w, v, m, c, τ, ε, Rinf, lev, Sφ, a, hgen, hw_det, hw_prim, ne_of_gt hc, hR, hmw, hmvl,
    hlev, hexh, hgap, hbase, hinf, hline, hcover⟩⟩

/-! ### Hole 2 without `hstrict`: the break row sits below the seed corner (2026-09-26)

Collé's Figure 11(B) (`b3_colle2.txt:848-856`) fills the new row `𝓡^{N+1}_I \ 𝓡^N_I` from its
`ℓ_{I-1}`-end; the translate of `𝒮_φ` is placed at the corner where `𝓡_{I-1}`'s semi-infinite
`ℓ_{I-1}`-edge leaves the seed.  That room comes from the **seed `B` being `E(𝒮_φ)`-enveloped**
(`:777`/`:402`), not from any angular extremality of `a` — so `hstrict` (which, by
`CritIffTop.crit_iff_eq_top`, holds only at `I = len`) is not needed.  Two facts, both about the
explicit tower `Rinf = tower … (I+1)`:

* `tower_room.1`: `Rinf ∩ {dot m ≥ L0} ⊆ tower … I` for `L0 := dot m (faceStart B ν)`,
  `ν := dir (extChain (I+1))` — so any cut at level `≥ L0` is periodic, and the consumer's
  `¬ PeriodOn (cut (N+1))` forces `lev (N+1) < L0`;
* `tower_room.2`: below `L0`, `P + (b - a) ∈ Rinf` for all `b ∈ 𝒮_φ` (Minkowski translate
  `HsuppContain.hcont` + the cone `ℓB + cone(wtower I, w)` + lattice convexity).

Numerics (硬规矩 6): `tmp/wip/hole2-corner-bench.py`, 2439 benches (4-gen `(1,0),(0,1),(2,-1),(3,-1)`,
a hexagon family and a 5-generator family, zonotope and non-zonotope `B`), all six ingredients
hold; `hstrict` holds in exactly the `I = len` cases (586/2439). -/
namespace Hole2Room


open Nivat.LE2 Nivat.ConeRegion

/-! ## §1  Two general facts about finite lattice-convex polygons -/

/-- Every nonzero `ν` has an edge normal strictly on its clockwise side. -/
theorem exists_mem_E_det_pos {T : Set (ℤ × ℤ)} (hTfin : T.Finite) (hTne : T.Nonempty)
    (hTarea : PosArea T) {ν : ℤ × ℤ} (hν : ν ≠ 0) : ∃ μ ∈ E T, 0 < det μ ν := by
  have hpne : dir (-ν) ≠ 0 := Nivat.PolyChainSum.dir_ne_zero (neg_ne_zero.mpr hν)
  have hpos : 0 < dot (dir (-ν)) (dir (-ν)) := by
    simp only [ne_eq, Prod.ext_iff, not_and_or] at hpne
    rcases hpne with h | h
    · simp only [dot]; nlinarith [mul_self_nonneg (dir (-ν)).2, mul_self_pos.mpr h]
    · simp only [dot]; nlinarith [mul_self_nonneg (dir (-ν)).1, mul_self_pos.mpr h]
  set c : ℝ × ℝ := toReal (dir (-ν)) with hcdef
  have hcne : c ≠ 0 := by
    intro hz
    apply hpne
    have h1 : ((dir (-ν)).1 : ℝ) = 0 := by
      have := congrArg Prod.fst hz; simpa [hcdef, toReal] using this
    have h2 : ((dir (-ν)).2 : ℝ) = 0 := by
      have := congrArg Prod.snd hz; simpa [hcdef, toReal] using this
    have e1 : (dir (-ν)).1 = 0 := by exact_mod_cast h1
    have e2 : (dir (-ν)).2 = 0 := by exact_mod_cast h2
    exact Prod.ext e1 e2
  obtain ⟨n1, n2, a, b, hn1, hn2, ha, hb, hc1, hc2, v, hvle, hvn1, hvn2⟩ :=
    isFrame_E hTfin hTne hTarea c hcne
  have hDc : ((-ν).1 : ℝ) * c.2 - ((-ν).2 : ℝ) * c.1 =
      a * ((det (-ν) n1 : ℤ) : ℝ) + b * ((det (-ν) n2 : ℤ) : ℝ) := by
    have e1 : ((det (-ν) n1 : ℤ) : ℝ) = ((-ν).1 : ℝ) * (n1.2 : ℝ) - ((-ν).2 : ℝ) * (n1.1 : ℝ) := by
      simp only [det]; push_cast; ring
    have e2 : ((det (-ν) n2 : ℤ) : ℝ) = ((-ν).1 : ℝ) * (n2.2 : ℝ) - ((-ν).2 : ℝ) * (n2.1 : ℝ) := by
      simp only [det]; push_cast; ring
    rw [e1, e2, hc1, hc2]; ring
  have hval : ((-ν).1 : ℝ) * c.2 - ((-ν).2 : ℝ) * c.1 = ((det (-ν) (dir (-ν)) : ℤ) : ℝ) := by
    simp only [hcdef, toReal, det]; push_cast; ring
  have hdd : det (-ν) (dir (-ν)) = dot (dir (-ν)) (dir (-ν)) :=
    (Nivat.PolyChainSum.dot_dir_left (-ν) (dir (-ν))).symm
  have hDcpos : (0 : ℝ) < ((-ν).1 : ℝ) * c.2 - ((-ν).2 : ℝ) * c.1 := by
    rw [hval, hdd]; exact_mod_cast hpos
  rw [hDc] at hDcpos
  have hflip : ∀ n : ℤ × ℤ, det (-ν) n = det n ν := by
    intro n; simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
  have hexists : 0 < det (-ν) n1 ∨ 0 < det (-ν) n2 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    have h1' : ((det (-ν) n1 : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h1
    have h2' : ((det (-ν) n2 : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h2
    nlinarith [mul_nonneg ha (neg_nonneg.mpr h1'), mul_nonneg hb (neg_nonneg.mpr h2')]
  rcases hexists with h | h
  · exact ⟨n1, hn1, by rw [← hflip]; exact h⟩
  · exact ⟨n2, hn2, by rw [← hflip]; exact h⟩

/-- **Normal-cone form of fan adjacency.**  If no edge normal of `S` lies strictly between a
direction `n0` and an edge normal `ν` (counter-clockwise), then the start of `S`'s `ν`-face
maximises `dot n0` over `S` — `n0` need **not** be an edge normal.  The proof picks the
clockwise fan-neighbour `νa` of `ν` (`PolyChainSum.exists_max_det`), shares the vertex
(`PolyChain.adjacent_shared_vertex`), and writes `n0` in the cone `(νa, ν)` by Cramer. -/
theorem faceStart_max_of_no_between {S : Set (ℤ × ℤ)} (hfin : S.Finite)
    (hlc : IsLatticeConvexRegion S) {n0 ν : ℤ × ℤ} (hν : ν ∈ E S)
    (hne : ∃ μ ∈ E S, 0 < det μ ν) (hn0 : 0 < det n0 ν)
    (hnb : ∀ μ ∈ E S, ¬ (0 < det n0 μ ∧ 0 < det μ ν)) :
    ∀ z ∈ S, dot n0 z ≤ dot n0 (Nivat.PolyChain.faceStart S ν) := by
  classical
  set A : Finset (ℤ × ℤ) :=
    (finite_E_of_finite hfin).toFinset.filter (fun μ => 0 < det μ ν) with hA
  have hAne : A.Nonempty := by
    obtain ⟨μ, hμ, hpos⟩ := hne
    exact ⟨μ, Finset.mem_filter.mpr ⟨(finite_E_of_finite hfin).mem_toFinset.mpr hμ, hpos⟩⟩
  have hνne : ν ≠ 0 := (mem_E_iff.mp hν).1.ne_zero
  have hAe : ∀ μ ∈ A, 0 < det (-ν) μ := by
    intro μ hμ
    have h1 := (Finset.mem_filter.mp hμ).2
    have h2 : det (-ν) μ = det μ ν := by simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
    rw [h2]; exact h1
  obtain ⟨νa, hνaA, hmax⟩ :=
    Nivat.PolyChainSum.exists_max_det (neg_ne_zero.mpr hνne) hAe hAne
  obtain ⟨hνaE', hνadet⟩ := Finset.mem_filter.mp hνaA
  have hνaE : νa ∈ E S := (finite_E_of_finite hfin).mem_toFinset.mp hνaE'
  have hadj : ∀ μ ∈ E S, ¬ (0 < det νa μ ∧ 0 < det μ ν) := by
    rintro μ hμ ⟨h1, h2⟩
    exact hmax μ (Finset.mem_filter.mpr ⟨(finite_E_of_finite hfin).mem_toFinset.mpr hμ, h2⟩) h1
  have hshare := Nivat.PolyChain.adjacent_shared_vertex hfin hlc hνaE hν hνadet hadj
  have hℓa : Nivat.PolyChain.faceStart S ν ∈ face S νa := by
    rw [← hshare]; exact Nivat.PolyChain.faceEnd_mem hlc hfin hνaE
  have hℓb : Nivat.PolyChain.faceStart S ν ∈ face S ν := Nivat.PolyChain.faceStart_mem hfin hν
  have hcone : 0 ≤ det νa n0 := by
    by_contra hlt
    push_neg at hlt
    apply hnb νa hνaE
    refine ⟨?_, hνadet⟩
    have hsk : det n0 νa = - det νa n0 := by simp only [det]; ring
    rw [hsk]; linarith
  intro z hz
  set ℓ := Nivat.PolyChain.faceStart S ν with hℓdef
  have h1 : dot νa z ≤ dot νa ℓ := hℓa.2 z hz
  have h2 : dot ν z ≤ dot ν ℓ := hℓb.2 z hz
  have hcr : det νa ν * (dot n0 z - dot n0 ℓ) =
      det n0 ν * (dot νa z - dot νa ℓ) + det νa n0 * (dot ν z - dot ν ℓ) := by
    simp only [det, dot]; ring
  have hA1 : det n0 ν * (dot νa z - dot νa ℓ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hn0.le (by linarith)
  have hA2 : det νa n0 * (dot ν z - dot ν ℓ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hcone (by linarith)
  have hprod : det νa ν * (dot n0 z - dot n0 ℓ) ≤ 0 := by rw [hcr]; linarith
  by_contra hgt
  push_neg at hgt
  have : 0 < det νa ν * (dot n0 z - dot n0 ℓ) := mul_pos hνadet (by linarith)
  linarith

/-! ## §2  The tower chain, in the branch `det u' vl = -1`

`extChain … j` for `j ≤ len + 1` (with `extChain … (len + 1) = wtower … len = -vl`) is strictly
`det`-increasing.  Every edge normal of `B` (equivalently of `𝒮_φ`) is `± dir (extChain … j)`
for such a `j`, so consecutive chain directions have **no** edge normal strictly between their
`dir`s.  This is the only angular input of the room argument below. -/

section Chain


theorem det_neg_right' (a b : ℤ × ℤ) : det a (-b) = - det a b := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

theorem det_neg_left' (a b : ℤ × ℤ) : det (-a) b = - det a b := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

theorem dir_neg' (a : ℤ × ℤ) : dir (-a) = - dir a := by
  simp only [dir, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk]

theorem extChain_last (d : DecompData ξ) (nℓ vl u' : ℤ × ℤ) (i : Fin d.m) :
    extChain d nℓ vl u' i ((sortedCand d nℓ u' i).length + 1) = -vl :=
  wtower_last d nℓ vl u' i

/-- **Chain order**, including the appended `-vl` at `len + 1`. -/
theorem chain_order {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hdetu : det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {j k : ℕ} (hjk : j < k) (hk : k ≤ (sortedCand d nℓ u' i).length + 1) :
    0 < det (extChain d nℓ vl u' i j) (extChain d nℓ vl u' i k) := by
  have hunimod : det u' vl = 1 ∨ det u' vl = -1 := Or.inr hdetu
  have hneg1 : det u' (-vl) = 1 := by rw [det_neg_right', hdetu]; norm_num
  rcases Nat.lt_or_ge k ((sortedCand d nℓ u' i).length + 1) with hlt | hge
  · have h := det_pos_extChain d hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu hnℓ_ne
      hjk (by omega)
    rw [hneg1, mul_one] at h
    exact h
  · have hkeq : k = (sortedCand d nℓ u' i).length + 1 := by omega
    subst hkeq
    rw [extChain_last]
    cases j with
    | zero => show 0 < det u' (-vl); rw [hneg1]; norm_num
    | succ t =>
      show 0 < det (wtower d nℓ vl u' i t) (-vl)
      have ht : t < (sortedCand d nℓ u' i).length := by omega
      exact (det_w_negvl_sign_eq d hvl_prim hprim hperp i hdoth hnu (mem_candSet_wtower ht)).mpr
        (by rw [hneg1]; norm_num)

theorem lt_of_det_ext_pos {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hdetu : det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {j k : ℕ} (hj : j ≤ (sortedCand d nℓ u' i).length + 1)
    (h : 0 < det (extChain d nℓ vl u' i j) (extChain d nℓ vl u' i k)) : j < k := by
  rcases lt_trichotomy j k with h1 | h1 | h1
  · exact h1
  · subst h1; simp only [det] at h; linarith
  · have h2 := chain_order d hvl_prim hprim hperp henv i hdoth hadjB hdetu hnu hnℓ_ne h1 hj
    rw [det_skew] at h2
    linarith

theorem lt_of_det_ext_neg {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hdetu : det u' vl = -1) (hnu : dot nℓ u' < 0) (hnℓ_ne : nℓ ≠ 0)
    {j k : ℕ} (hk : k ≤ (sortedCand d nℓ u' i).length + 1)
    (h : det (extChain d nℓ vl u' i j) (extChain d nℓ vl u' i k) < 0) : k < j := by
  have h' : 0 < det (extChain d nℓ vl u' i k) (extChain d nℓ vl u' i j) := by
    rw [det_skew]; linarith
  exact lt_of_det_ext_pos d hvl_prim hprim hperp henv i hdoth hadjB hdetu hnu hnℓ_ne hk h'

/-- `nℓ` is an edge normal of `B`: it is `± genPerp' (h i)`. -/
theorem nl_mem_E_B {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0) : nℓ ∈ E B := by
  have hfin : (E (↑d.Sphi : Set (ℤ × ℤ))).Finite := finite_E_of_finite d.Sphi.finite_toSet
  have hE : E B = E (↑d.Sphi : Set (ℤ × ℤ)) := Enveloped.E_eq hfin henv
  obtain ⟨c, hci⟩ := h_i_eq_zsmul_vl d hvl_prim hprim hperp i hdoth
  have hpar : det vl (d.h i) = 0 := by
    rw [hci]; simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have hg : dot (genPerp' (d.h i)) vl = 0 :=
    Nivat.LaneTowerHlevGen.dot_genPerp'_eq_zero_of_par d i hvl_prim hpar
  have hvl0 : vl ≠ 0 := hvl_prim.ne_zero
  have hdet : det nℓ (genPerp' (d.h i)) = 0 :=
    det_eq_zero_of_dot_eq_zero hvl0 (by rw [dot_comm]; exact hperp) (by rw [dot_comm]; exact hg)
  rcases eq_or_neg_of_prim_of_det_eq_zero hprim (genPerp'_prim (d.h_ne i)) hdet with h | h
  · rw [hE, ← h]; exact (genPerp'_mem_E_Sphi d i).1
  · have : nℓ = - genPerp' (d.h i) := by rw [h]; simp
    rw [hE, this]; exact (genPerp'_mem_E_Sphi d i).2

/-- **Edge normals are `± dir (extChain j)`**, `j ≤ len + 1`. -/
theorem ext_cases_of_mem_E_B {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hdetu : det u' vl = -1) (hnl : nℓ = - dir vl) {μ : ℤ × ℤ} (hμ : μ ∈ E B) :
    ∃ j, j ≤ (sortedCand d nℓ u' i).length + 1 ∧
      (μ = dir (extChain d nℓ vl u' i j) ∨ μ = - dir (extChain d nℓ vl u' i j)) := by
  have hunimod : det u' vl = 1 ∨ det u' vl = -1 := Or.inr hdetu
  have hpos : 0 < det u' (-vl) := by rw [det_neg_right', hdetu]; norm_num
  have hlast : dir (extChain d nℓ vl u' i ((sortedCand d nℓ u' i).length + 1)) = nℓ := by
    rw [extChain_last, dir_neg', hnl]
  have h0 : dir (extChain d nℓ vl u' i 0) = genPerp' u' :=
    (genPerp'_eq_dir_of_prim (prim_u'_of_hunimod hunimod)).symm
  have hm : ∀ m, m < (sortedCand d nℓ u' i).length →
      dir (extChain d nℓ vl u' i (m + 1)) = nprevOf d nℓ vl u' i m := by
    intro m hmlen
    unfold nprevOf
    rw [if_pos hpos]
    exact (genPerp'_eq_dir_of_prim (prim_iff_primitive.mpr
      (prim_of_mem_candSet d hvl_prim hprim hperp i hdoth (mem_candSet_wtower hmlen)))).symm
  rcases cases_of_mem_E_B d hvl_prim hprim hperp henv i hdoth hμ with hnl' | hu' | ⟨m, hmlen, hmeq⟩
  · refine ⟨(sortedCand d nℓ u' i).length + 1, le_refl _, ?_⟩
    rw [hlast]; exact hnl'
  · refine ⟨0, Nat.zero_le _, ?_⟩
    rw [h0]; exact hu'
  · refine ⟨m + 1, by omega, ?_⟩
    rw [hm m hmlen]; exact hmeq

/-- **No edge normal strictly between consecutive chain `dir`s.** -/
theorem no_between_ext {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hdetu : det u' vl = -1) (hnu : dot nℓ u' < 0) (hnl : nℓ = - dir vl)
    {I : ℕ} (hI : I ≤ (sortedCand d nℓ u' i).length) :
    ∀ μ ∈ E B, ¬ (0 < det (dir (extChain d nℓ vl u' i I)) μ ∧
      0 < det μ (dir (extChain d nℓ vl u' i (I + 1)))) := by
  have hnℓ_ne : nℓ ≠ 0 := (prim_iff_primitive.mp hprim).ne_zero
  rintro μ hμ ⟨h1, h2⟩
  obtain ⟨j, hj, hμeq | hμeq⟩ :=
    ext_cases_of_mem_E_B d hvl_prim hprim hperp henv i hdoth hdetu hnl hμ
  · rw [hμeq, det_dir_dir] at h1 h2
    have a1 := lt_of_det_ext_pos d hvl_prim hprim hperp henv i hdoth hadjB hdetu hnu hnℓ_ne
      (by omega) h1
    have a2 := lt_of_det_ext_pos d hvl_prim hprim hperp henv i hdoth hadjB hdetu hnu hnℓ_ne
      hj h2
    omega
  · rw [hμeq, det_neg_right', det_dir_dir] at h1
    rw [hμeq, det_neg_left', det_dir_dir] at h2
    have h1' : det (extChain d nℓ vl u' i I) (extChain d nℓ vl u' i j) < 0 := by linarith
    have h2' : det (extChain d nℓ vl u' i j) (extChain d nℓ vl u' i (I + 1)) < 0 := by linarith
    have a1 := lt_of_det_ext_neg d hvl_prim hprim hperp henv i hdoth hadjB hdetu hnu hnℓ_ne
      (j := I) (k := j) hj h1'
    have a2 := lt_of_det_ext_neg d hvl_prim hprim hperp henv i hdoth hadjB hdetu hnu hnℓ_ne
      (j := j) (k := I + 1) (by omega) h2'
    omega

/-- `dir (extChain (I+1))` is an edge normal of `B` for every `I ≤ len`. -/
theorem dir_ext_succ_mem_E_B {B : Set (ℤ × ℤ)} (d : DecompData ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : EnvOf (↑d.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.m) (hdoth : dot nℓ (d.h i) = 0)
    (hdetu : det u' vl = -1) (hnl : nℓ = - dir vl)
    {I : ℕ} (hI : I ≤ (sortedCand d nℓ u' i).length) :
    dir (extChain d nℓ vl u' i (I + 1)) ∈ E B := by
  have hpos : 0 < det u' (-vl) := by rw [det_neg_right', hdetu]; norm_num
  rcases Nat.lt_or_ge I (sortedCand d nℓ u' i).length with hlt | hge
  · have heq : dir (extChain d nℓ vl u' i (I + 1)) = nprevOf d nℓ vl u' i I := by
      unfold nprevOf
      rw [if_pos hpos]
      exact (genPerp'_eq_dir_of_prim (prim_iff_primitive.mpr
        (prim_of_mem_candSet d hvl_prim hprim hperp i hdoth (mem_candSet_wtower hlt)))).symm
    rw [heq]; exact nprevOf_mem_E_B d hvl_prim hprim hperp henv i hdoth hlt
  · have hIeq : I = (sortedCand d nℓ u' i).length := by omega
    subst hIeq
    rw [extChain_last, dir_neg', ← hnl]
    exact nl_mem_E_B d hvl_prim hprim hperp henv i hdoth

end Chain

/-! ## §3  The corner, the Minkowski translate, and room below the corner

Everything is stated at the explicit tower `𝓡_I := tower (coneRegion B vl u') wtower I` with
`Rinf := tower … (I+1) = sweep 𝓡_I (wtower I)`, `w := extChain I`, `m := expNormal w vl`,
`ν := dir (extChain (I+1))`, `ℓB := faceStart B ν` and `L0 := dot m ℓB`:

* `Rinf ∩ {dot m ≥ L0} ⊆ 𝓡_I` (`TowerHBaseMin.cut_step_subset_of_cut` at the corner `ℓB` and
  the normal `ν`), so every cut at a level `≥ L0` inherits `𝓡_I`'s period;
* below `L0`, `Rinf` is the cone `ℓB + cone(wtower I, w)`, and `𝒮_φ + (ℓB - a) ⊆ B`
  (`HsuppContain.hcont`, after `corner_eq_faceStart` pins the generating-package corner `a`
  to `faceStart 𝒮_φ ν`), so `P + (b - a) ∈ Rinf` for every `P ∈ Rinf` with `dot m P < L0`.

No `hstrict`/`hnlmax`/`hwadj`-type hypothesis appears: the angular input is only
`no_between_ext` (consecutive chain directions), which is the construction of `wtower`. -/

section Room


theorem expNormal_eq_smul_dir (w vl : ℤ × ℤ) : expNormal w vl = det w vl • dir w := rfl

theorem dot_expNormal_eq (w vl z : ℤ × ℤ) :
    dot (expNormal w vl) z = det w vl * det w z := by
  rw [expNormal_eq_smul_dir, dot_smul, Nivat.PolyChainSum.dot_dir_left]

/-- **The generating-package corner is the start of `𝒮_φ`'s `dir (extChain (I+1))`-face.** -/
theorem corner_eq_faceStart {B : Set (ℤ × ℤ)} (d : DecompDataZ ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) B)
    (i : Fin d.toDecompData.m) (hdoth : dot nℓ (d.toDecompData.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hdetu : det u' vl = -1) (hnu : dot nℓ u' < 0) (hnl : nℓ = - dir vl)
    {I : ℕ} (hI : I ≤ (sortedCand d.toDecompData nℓ u' i).length)
    {a : ℤ × ℤ} (ha : a ∈ d.toDecompData.Sphi)
    (ha_min : ∀ b ∈ d.toDecompData.Sphi,
      dot (expNormal (extChain d.toDecompData nℓ vl u' i I) vl) a ≤
        dot (expNormal (extChain d.toDecompData nℓ vl u' i I) vl) b)
    (ha_end : ∀ b ∈ d.toDecompData.Sphi,
      dot (expNormal (extChain d.toDecompData nℓ vl u' i I) vl) b =
        dot (expNormal (extChain d.toDecompData nℓ vl u' i I) vl) a →
      ∃ t : ℕ, b = a + (t : ℤ) • extChain d.toDecompData nℓ vl u' i I) :
    a = Nivat.PolyChain.faceStart (↑d.toDecompData.Sphi : Set (ℤ × ℤ))
      (dir (extChain d.toDecompData nℓ vl u' i (I + 1))) := by
  set w := extChain d.toDecompData nℓ vl u' i I with hw
  set ν := dir (extChain d.toDecompData nℓ vl u' i (I + 1)) with hν
  set S : Set (ℤ × ℤ) := ↑d.toDecompData.Sphi with hS
  have hnℓ_ne : nℓ ≠ 0 := (prim_iff_primitive.mp hprim).ne_zero
  have hSfin : S.Finite := d.toDecompData.Sphi.finite_toSet
  have hSlc : IsLatticeConvexRegion S := Nivat.ChainAsm.isLatticeConvexRegion_coe d.Sphi_conv
  have hSarea : PosArea S := Nivat.AhatMono.posArea_Sphi d.toDecompData
  have hSne : S.Nonempty := ⟨a, ha⟩
  have hE : E B = E S := Enveloped.E_eq (finite_E_of_finite hSfin) henv
  have hνS : ν ∈ E S := by
    rw [← hE]
    exact dir_ext_succ_mem_E_B d.toDecompData hvl_prim hprim hperp henv i hdoth hdetu hnl hI
  have hνne : ν ≠ 0 := (mem_E_iff.mp hνS).1.ne_zero
  have hn0 : 0 < det (dir w) ν := by
    rw [hν, det_dir_dir]
    exact chain_order d.toDecompData hvl_prim hprim hperp henv i hdoth hadjB hdetu hnu hnℓ_ne
      (Nat.lt_succ_self I) (by omega)
  have hnb : ∀ μ ∈ E S, ¬ (0 < det (dir w) μ ∧ 0 < det μ ν) := fun μ hμ =>
    no_between_ext d.toDecompData hvl_prim hprim hperp henv i hdoth hadjB hdetu hnu hnl hI μ
      (hE ▸ hμ)
  have hmax := faceStart_max_of_no_between hSfin hSlc hνS
    (exists_mem_E_det_pos hSfin hSne hSarea hνne) hn0 hnb
  have hℓface : Nivat.PolyChain.faceStart S ν ∈ face S ν :=
    Nivat.PolyChain.faceStart_mem hSfin hνS
  have hℓS : Nivat.PolyChain.faceStart S ν ∈ d.toDecompData.Sphi := hℓface.1
  have hwvl : det w vl < 0 := by
    have h := chain_order d.toDecompData hvl_prim hprim hperp henv i hdoth hadjB hdetu hnu hnℓ_ne
      (j := I) (k := (sortedCand d.toDecompData nℓ u' i).length + 1) (by omega) le_rfl
    rw [extChain_last, det_neg_right'] at h
    linarith
  have hlvl : dot (expNormal w vl) (Nivat.PolyChain.faceStart S ν) = dot (expNormal w vl) a := by
    have h1 := ha_min _ hℓS
    have h2 := hmax a ha
    rw [Nivat.PolyChainSum.dot_dir_left, Nivat.PolyChainSum.dot_dir_left] at h2
    rw [dot_expNormal_eq, dot_expNormal_eq] at h1 ⊢
    nlinarith
  obtain ⟨t, ht⟩ := ha_end _ hℓS hlvl
  have hνa : dot ν a ≤ dot ν (Nivat.PolyChain.faceStart S ν) := hℓface.2 a ha
  have hνw : dot ν w < 0 := by
    rw [hν, Nivat.PolyChainSum.dot_dir_left]
    have h := chain_order d.toDecompData hvl_prim hprim hperp henv i hdoth hadjB hdetu hnu hnℓ_ne
      (Nat.lt_succ_self I) (by omega)
    rw [det_skew] at h
    linarith
  rw [ht, dot_add, dot_comm ν ((t : ℤ) • w), dot_smul, dot_comm w ν] at hνa
  have ht0 : (t : ℤ) = 0 := by
    have htnn : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
    nlinarith
  rw [ht, ht0, zero_smul, add_zero]

/-- **Minkowski translate** (`HsuppContain.hcont` at the normal `ν`): `𝒮_φ` shifted so that its
`ν`-face start sits on `B`'s `ν`-face start lies inside `B`. -/
theorem sphi_shift_subset {B : Set (ℤ × ℤ)} (d : DecompDataZ ξ)
    (henv : EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) B) (hBfin : B.Finite)
    {ν : ℤ × ℤ} (hνS : ν ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ))) :
    ∀ b ∈ (↑d.toDecompData.Sphi : Set (ℤ × ℤ)),
      Nivat.PolyChain.faceStart B ν +
        (b - Nivat.PolyChain.faceStart (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) ν) ∈ B := by
  set S : Set (ℤ × ℤ) := ↑d.toDecompData.Sphi with hS
  have hSfin : S.Finite := d.toDecompData.Sphi.finite_toSet
  have hSlc : IsLatticeConvexRegion S := Nivat.ChainAsm.isLatticeConvexRegion_coe d.Sphi_conv
  have hSarea : PosArea S := Nivat.AhatMono.posArea_Sphi d.toDecompData
  have hE : E B = E S := Enveloped.E_eq (finite_E_of_finite hSfin) henv
  have hνB : ν ∈ E B := hE ▸ hνS
  have hBarea : PosArea B := Nivat.AhatMono.posArea_of_enveloped hSfin hSarea henv
  have hlcB : IsLatticeConvexRegion B := henv.1.1
  have hBne : B.Nonempty := by obtain ⟨p, hp, -⟩ := hBarea; exact ⟨p, hp⟩
  have hνne : ν ≠ 0 := (mem_E_iff.mp hνS).1.ne_zero
  have hdom : ∀ n ∈ E B, (face S n).encard ≤ (face B n).encard :=
    fun n hn => (henv.1.2 n hn).2
  -- the two face-starts, in `hcont`'s `(m, w) := (-ν, dir ν)` convention
  have hend : ∀ {T : Set (ℤ × ℤ)}, T.Finite → IsLatticeConvexRegion T → ν ∈ E T →
      (∀ b ∈ T, dot (-ν) (Nivat.PolyChain.faceStart T ν) ≤ dot (-ν) b) ∧
      (∀ b ∈ T, dot (-ν) b = dot (-ν) (Nivat.PolyChain.faceStart T ν) →
        ∃ t : ℕ, b = Nivat.PolyChain.faceStart T ν + (t : ℤ) • dir ν) := by
    intro T hTfin hTlc hνT
    have hface := Nivat.PolyChain.faceStart_mem hTfin hνT
    refine ⟨fun b hb => ?_, fun b hb hbeq => ?_⟩
    · rw [dot_neg_left, dot_neg_left]; linarith [hface.2 b hb]
    · rw [dot_neg_left, dot_neg_left] at hbeq
      have hbface : b ∈ face T ν := ⟨hb, fun y hy => by linarith [hface.2 y hy]⟩
      rw [Nivat.PolyChain.face_eq_segment hTlc hTfin hνT] at hbface
      obtain ⟨t, -, ht⟩ := hbface
      exact ⟨t, ht⟩
  obtain ⟨hSmin, hSend⟩ := hend hSfin hSlc hνS
  obtain ⟨hBmin, hBend⟩ := hend hBfin hlcB hνB
  exact Nivat.HsuppContain.hcont d hBfin hBne hBarea hlcB (m := -ν) (w := dir ν)
    (by rw [neg_neg]) (neg_ne_zero.mpr hνne) hE (by rw [neg_neg]; exact hνS) hdom
    (Nivat.PolyChain.faceStart_mem hSfin hνS).1 hSmin hSend
    (Nivat.PolyChain.faceStart_mem hBfin hνB).1 hBmin hBend

theorem dot_dir_self' (a : ℤ × ℤ) : dot (dir a) a = 0 := by simp only [dot, dir]; ring

/-- **The tower's room statement, at the explicit tower index `I`.**

`L0 := dot m (faceStart B ν)` with `ν := dir (extChain (I+1))`.
(1) the part of `Rinf := tower (I+1)` at `m`-level `≥ L0` lies in `tower I`;
(2) below `L0`, `Rinf` has room for the whole `𝒮_φ − a` for the generating-package corner `a`. -/
theorem tower_room {B : Set (ℤ × ℤ)} (d : DecompDataZ ξ) {vl nℓ u' : ℤ × ℤ}
    (hvl_prim : Primitive vl) (hprim : Prim nℓ) (hperp : dot nℓ vl = 0)
    (henv : EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) B) (hBfin : B.Finite)
    (i : Fin d.toDecompData.m) (hdoth : dot nℓ (d.toDecompData.h i) = 0)
    (hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u'))
    (hdetu : det u' vl = -1) (hnu : dot nℓ u' < 0) (hnl : nℓ = - dir vl)
    {I : ℕ} (hI : I ≤ (sortedCand d.toDecompData nℓ u' i).length)
    (hconvAll : ∀ n : ℕ, n ≤ (sortedCand d.toDecompData nℓ u' i).length + 1 →
      IsLatticeConvexRegion
        (tower (coneRegion B vl u') (wtower d.toDecompData nℓ vl u' i) n)) :
    (∀ z ∈ tower (coneRegion B vl u') (wtower d.toDecompData nℓ vl u' i) (I + 1),
        dot (expNormal (extChain d.toDecompData nℓ vl u' i I) vl)
            (Nivat.PolyChain.faceStart B (dir (extChain d.toDecompData nℓ vl u' i (I + 1)))) ≤
          dot (expNormal (extChain d.toDecompData nℓ vl u' i I) vl) z →
        z ∈ tower (coneRegion B vl u') (wtower d.toDecompData nℓ vl u' i) I) ∧
    (∀ a ∈ d.toDecompData.Sphi,
      (∀ b ∈ d.toDecompData.Sphi,
        dot (expNormal (extChain d.toDecompData nℓ vl u' i I) vl) a ≤
          dot (expNormal (extChain d.toDecompData nℓ vl u' i I) vl) b) →
      (∀ b ∈ d.toDecompData.Sphi,
        dot (expNormal (extChain d.toDecompData nℓ vl u' i I) vl) b =
          dot (expNormal (extChain d.toDecompData nℓ vl u' i I) vl) a →
        ∃ t : ℕ, b = a + (t : ℤ) • extChain d.toDecompData nℓ vl u' i I) →
      ∀ P ∈ tower (coneRegion B vl u') (wtower d.toDecompData nℓ vl u' i) (I + 1),
        dot (expNormal (extChain d.toDecompData nℓ vl u' i I) vl) P <
          dot (expNormal (extChain d.toDecompData nℓ vl u' i I) vl)
            (Nivat.PolyChain.faceStart B (dir (extChain d.toDecompData nℓ vl u' i (I + 1)))) →
        ∀ b ∈ d.toDecompData.Sphi,
          P + (b - a) ∈ tower (coneRegion B vl u') (wtower d.toDecompData nℓ vl u' i) (I + 1)) := by
  set len := (sortedCand d.toDecompData nℓ u' i).length with hlen
  set wt := wtower d.toDecompData nℓ vl u' i with hwt
  set C := tower (coneRegion B vl u') wt I with hC
  set Rinf := tower (coneRegion B vl u') wt (I + 1) with hRinf
  set w := extChain d.toDecompData nℓ vl u' i I with hw
  set wI := extChain d.toDecompData nℓ vl u' i (I + 1) with hwI
  set m := expNormal w vl with hm
  set ν := dir wI with hν
  set ℓB := Nivat.PolyChain.faceStart B ν with hℓB
  have hnℓ_ne : nℓ ≠ 0 := (prim_iff_primitive.mp hprim).ne_zero
  have hunimod : det u' vl = 1 ∨ det u' vl = -1 := Or.inr hdetu
  have hwI_eq : wI = wt I := rfl
  have hSfin : (↑d.toDecompData.Sphi : Set (ℤ × ℤ)).Finite := d.toDecompData.Sphi.finite_toSet
  have hE : E B = E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) :=
    Enveloped.E_eq (finite_E_of_finite hSfin) henv
  have hνB : ν ∈ E B :=
    dir_ext_succ_mem_E_B d.toDecompData hvl_prim hprim hperp henv i hdoth hdetu hnl hI
  have hνS : ν ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) := hE ▸ hνB
  have hℓBface : ℓB ∈ face B ν := Nivat.PolyChain.faceStart_mem hBfin hνB
  -- `dot ν (extChain j) = - det (extChain j) wI < 0` for `j ≤ I`
  have hνext : ∀ j, j ≤ I → dot ν (extChain d.toDecompData nℓ vl u' i j) < 0 := by
    intro j hj
    rw [hν, Nivat.PolyChainSum.dot_dir_left]
    have h := chain_order d.toDecompData hvl_prim hprim hperp henv i hdoth hadjB hdetu hnu hnℓ_ne
      (j := j) (k := I + 1) (by omega) (by omega)
    rw [det_skew] at h
    linarith
  have hνvl : dot ν vl ≤ 0 := by
    rw [hν, Nivat.PolyChainSum.dot_dir_left]
    rcases Nat.lt_or_ge I len with hlt | hge
    · have h := chain_order d.toDecompData hvl_prim hprim hperp henv i hdoth hadjB hdetu hnu hnℓ_ne
        (j := I + 1) (k := len + 1) (by omega) le_rfl
      rw [extChain_last, det_neg_right'] at h
      linarith
    · have hIeq : I = len := by omega
      rw [hwI, hIeq, extChain_last]
      simp only [det, Prod.fst_neg, Prod.snd_neg]; nlinarith
  have hνwI : dot ν wI = 0 := by rw [hν]; exact dot_dir_self' wI
  have hνu' : dot ν u' < 0 := hνext 0 (Nat.zero_le _)
  have hprevC : ∀ q ∈ C, dot ν q ≤ dot ν ℓB := by
    refine Nivat.TowerHBaseMin.dot_le_of_mem_tower hνvl (le_of_lt hνu') wt I
      ?_ (fun b hb => hℓBface.2 b hb)
    intro k hk
    exact le_of_lt (hνext (k + 1) (by omega))
  have hmw : dot m w = 0 := Nivat.ColleReg.dot_expNormal_u'
  have hstep : dot m (wt I) < 0 :=
    Nivat.LaneTowerPkgMain.dot_m_step_neg d.toDecompData hvl_prim hprim hperp henv i hdoth hadjB
      hunimod hnu hnℓ_ne hI
  have hcutsub : ∀ z ∈ Rinf, dot m ℓB ≤ dot m z → z ∈ C := by
    intro z hz hlev
    refine Nivat.TowerHBaseMin.cut_step_subset_of_cut
      (isLatticeConvexRegion_inter_halfPlaneGE (hconvAll I (by omega)) m (dot m ℓB))
      (fun t => ?_) hmw hstep hprevC (hνext I le_rfl) (le_of_eq ?_) le_rfl hz hlev
    · have hℓcone : ℓB ∈ coneRegion B vl u' := by
        rw [mem_coneRegion_iff]; exact ⟨ℓB, hℓBface.1, 0, 0, by simp⟩
      exact Nivat.TowerHBaseMin.ray_mem_tower_extChain (nℓ := nℓ) d.toDecompData i I hℓcone t
    · rw [← hwI_eq]; exact hνwI
  refine ⟨hcutsub, ?_⟩
  intro a ha ha_min ha_end P hP hPlev b hb
  have haeq : a = Nivat.PolyChain.faceStart (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) ν :=
    corner_eq_faceStart d hvl_prim hprim hperp henv i hdoth hadjB hdetu hnu hnl hI ha ha_min
      ha_end
  set x := P - ℓB with hx
  set y := ℓB + (b - a) with hy
  have hyB : y ∈ B := by
    rw [hy, haeq]; exact sphi_shift_subset d henv hBfin hνS b hb
  have hycone : y ∈ coneRegion B vl u' := by
    rw [mem_coneRegion_iff]; exact ⟨y, hyB, 0, 0, by simp⟩
  have hyR : y ∈ Rinf := tower_monotone _ _ (Nat.zero_le (I + 1)) hycone
  -- `dot ν x ≤ 0`: `P = g + t • wI` with `g ∈ 𝓡_I`
  have hνx : dot ν x ≤ 0 := by
    obtain ⟨g, hg, t, rfl⟩ := hP
    have h1 := hprevC g hg
    rw [hx, dot_sub, dot_add, dot_comm ν ((t : ℤ) • wt I), dot_smul, dot_comm (wt I) ν,
      ← hwI_eq, hνwI]
    linarith
  have hmx : dot m x < 0 := by rw [hx, dot_sub]; linarith
  have hwvl : det w vl < 0 := by
    have h := chain_order d.toDecompData hvl_prim hprim hperp henv i hdoth hadjB hdetu hnu hnℓ_ne
      (j := I) (k := len + 1) (by omega) le_rfl
    rw [extChain_last, det_neg_right'] at h
    linarith
  have hD : 0 < det w wI :=
    chain_order d.toDecompData hvl_prim hprim hperp henv i hdoth hadjB hdetu hnu hnℓ_ne
      (Nat.lt_succ_self I) (by omega)
  have hα : 0 ≤ det x wI := by
    have : dot ν x = det wI x := Nivat.PolyChainSum.dot_dir_left wI x
    rw [det_skew]; linarith
  have hβ : 0 ≤ det w x := by
    have h := dot_expNormal_eq w vl x
    rw [← hm] at h
    rw [h] at hmx
    nlinarith
  have hcr : det w wI • x = det x wI • w + det w x • wI := by
    simp only [det, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    ext <;> simp <;> ring
  obtain ⟨α, hαeq⟩ := Int.eq_ofNat_of_zero_le hα
  obtain ⟨β, hβeq⟩ := Int.eq_ofNat_of_zero_le hβ
  have hfar : y + det w wI • x ∈ Rinf := by
    rw [hcr, hαeq, hβeq]
    have h1 : y + (α : ℤ) • w ∈ C := by
      have := Nivat.TowerHBaseMin.ray_mem_tower_extChain (nℓ := nℓ) d.toDecompData i I hycone α
      rw [← natCast_zsmul] at this
      exact this
    refine ⟨y + (α : ℤ) • w, h1, β, ?_⟩
    rw [← hwI_eq]; abel
  have hRlc : IsLatticeConvexRegion Rinf := hconvAll (I + 1) (by omega)
  have hmid := Nivat.LE2.mem_of_between hRlc (q := y) (e := x) (s := 0) (t := 1) (u := det w wI)
    (by simpa using hyR) hfar (by norm_num) (by omega)
  have hPeq : P + (b - a) = y + (1 : ℤ) • x := by rw [hy, hx, one_smul]; abel
  rw [hPeq]; exact hmid

end Room

/-! ## §4  The tower package with the room conjunct (13th)

Same binders as `LaneTowerPkgMain.lane_towerpkg_package_wid` plus `hdetpos` (already a binder
of the consumer `exists_cutResidualR_of_claim46`).  The body is `lane_towerpkg_reduce_wid` +
`lane_towerpkg_reduce_at_core` with `Rinf := tower … (I+1)` kept **explicit**, so that the 13th
conjunct (`tower_room`) can be stated about the very `Rinf` the first twelve talk about. -/

section Package


open Nivat.Colle41 Nivat.L1Region Nivat.LaneTowerPkgMain in
theorem package_room
    {e : ℤ × ℤ} (hξ : IsMinimalCounterexample ξ) (d : DecompDataZ ξ)
    {B : Set (ℤ × ℤ)} {u' nℓ vl : ℤ × ℤ} {c : ℤ}
    (henv : EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) B)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hvl_prim : Primitive vl) (hc : 0 < c)
    (hperp : dot nℓ vl = 0) (hdetpos : 0 < det nℓ vl) (hnu : dot nℓ u' = -1)
    (hbase₁ : PeriodOn (T e ξ) (coneRegion B vl u') (c • vl))
    (hprim : Prim nℓ) (i : Fin d.toDecompData.m)
    (hdoth : dot nℓ (d.toDecompData.h i) = 0)
    (hadj : ∀ n ∈ E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)),
      ¬ (dot n vl < 0 ∧ 0 < dot n u')) :
    ∃ (Rinf : Set (ℤ × ℤ)) (w : ℤ × ℤ), det vl w ≠ 0 ∧ Primitive w ∧
      ∃ (m : ℤ × ℤ), dot m w = 0 ∧ 0 < dot m vl ∧
      ∃ (b₀ : ℤ), Colle41.IsRegion Rinf vl w ∧
      (∃ z ∈ Rinf, dot m z = b₀) ∧
      (∀ b : ℤ, ∃ z ∈ Rinf, dot m z < b) ∧
      (∀ lev : ℕ → ℤ, lev 0 = b₀ → PeriodOn (T e ξ) (cut Rinf m lev 0) (c • vl)) ∧
      ¬ PeriodOn (T e ξ) Rinf (c • vl) ∧
      dot nℓ w < 0 ∧ (∃ top : ℤ, ∀ z ∈ Rinf, dot nℓ z ≤ top) ∧
      (∃ I : ℕ, I ≤ (sortedCand d.toDecompData nℓ u' i).length ∧
        w = extChain d.toDecompData nℓ vl u' i I) ∧
      (∃ L0 : ℤ,
        (∀ lev : ℕ → ℤ, ∀ n : ℕ, L0 ≤ lev n → PeriodOn (T e ξ) (cut Rinf m lev n) (c • vl)) ∧
        (∀ a ∈ d.toDecompData.Sphi, (∀ b ∈ d.toDecompData.Sphi, dot m a ≤ dot m b) →
          (∀ b ∈ d.toDecompData.Sphi, dot m b = dot m a → ∃ t : ℕ, b = a + (t : ℤ) • w) →
          ∀ P ∈ Rinf, dot m P < L0 → ∀ b ∈ d.toDecompData.Sphi, P + (b - a) ∈ Rinf)) := by
  obtain ⟨hnl, hdetu⟩ := Nivat.RegionNlDict.nl_eq_neg_dir_vl_and_det_u' hvl_prim hperp hdetpos hnu
  have hlevB : ∀ n, n < (sortedCand d.toDecompData nℓ u' i).length →
      Nivat.RegionSweep.LevelInterval B (wtower d.toDecompData nℓ vl u' i n) :=
    fun n _ => Nivat.LaneTowerHlevGen.levelInterval_wtower d.toDecompData henv hvl_prim hprim
      hperp i hdoth u' n
  have hnu' : dot nℓ u' < 0 := by omega
  have hnℓ_ne : nℓ ≠ 0 := hprim.ne_zero
  have hadjB : ∀ n ∈ E B, ¬ (dot n vl < 0 ∧ 0 < dot n u') := hadjB_of_hadj d.toDecompData henv hadj
  have hconvAll : ∀ n : ℕ, n ≤ (sortedCand d.toDecompData nℓ u' i).length + 1 →
      IsLatticeConvexRegion (tower (coneRegion B vl u') (wtower d.toDecompData nℓ vl u' i) n) :=
    fun n _ => hconv_of_levelB d.toDecompData henv hBfin hBne hunimod hvl_prim hperp hnu' hprim i
      hdoth hadjB hlevB n
  have hu'_prim : Primitive u' := prim_iff_primitive.mp (prim_u'_of_hunimod hunimod)
  have hvl_neg_prim : Primitive (-vl) := by
    obtain ⟨a, b, hab⟩ := hvl_prim
    exact ⟨-a, -b, by simp only [Prod.fst_neg, Prod.snd_neg]; linear_combination hab⟩
  have hw_prim_all : ∀ k, Primitive (wtower d.toDecompData nℓ vl u' i k) := by
    intro k
    by_cases hk : k < (sortedCand d.toDecompData nℓ u' i).length
    · exact prim_of_mem_candSet d.toDecompData hvl_prim hprim hperp i hdoth (mem_candSet_wtower hk)
    · have heq : wtower d.toDecompData nℓ vl u' i k = -vl := by
        simp only [wtower]; rw [dif_neg hk]
      rw [heq]; exact hvl_neg_prim
  have h_last : wtower d.toDecompData nℓ vl u' i (Mtower d.toDecompData nℓ u' i - 1) = -vl := by
    have hMeq : Mtower d.toDecompData nℓ u' i - 1 = (sortedCand d.toDecompData nℓ u' i).length := by
      simp only [Mtower]; omega
    rw [hMeq]; exact wtower_last d.toDecompData nℓ vl u' i
  have hM_pos : Mtower d.toDecompData nℓ u' i > 0 := by simp only [Mtower]; omega
  have hcvl_ne : c • vl ≠ 0 := smul_ne_zero (by omega) hvl_prim.ne_zero
  have htopHP : ∀ R w' c'', w' ≠ 0 → dot w' (c • vl) = 0 →
      {z | c'' ≤ dot w' z} ⊆ R → ¬ PeriodOn (T e ξ) R (c • vl) := by
    intro R w' c'' hw'0 hw'cvl hsub
    exact Nivat.HalfPlaneNotPeriodOn.not_periodOn_of_halfPlane_subset hξ e hw'0 hcvl_ne hw'cvl
      hsub
  obtain ⟨I, hIM, hper, hnper⟩ :=
    exists_tower_index hBfin hBne hvl_prim hu'_prim hunimod (wtower d.toDecompData nℓ vl u' i)
      hw_prim_all hM_pos h_last hbase₁ htopHP
  have hIlen : I ≤ (sortedCand d.toDecompData nℓ u' i).length := by
    simp only [Mtower] at hIM; omega
  -- ⟨explicit witnesses⟩
  have hwneg : dot nℓ (extChain d.toDecompData nℓ vl u' i I) < 0 :=
    dot_extChain_neg d.toDecompData hvl_prim hprim hperp i hdoth hnu' hIlen
  have hwvl_ne : det (extChain d.toDecompData nℓ vl u' i I) vl ≠ 0 :=
    det_ne_zero_of_dot_nl_neg hvl_prim hperp hwneg
  have hdet : det vl (extChain d.toDecompData nℓ vl u' i I) ≠ 0 := by
    intro h0; apply hwvl_ne
    have hskew := det_skew (extChain d.toDecompData nℓ vl u' i I) vl
    omega
  have hw_prim : Primitive (extChain d.toDecompData nℓ vl u' i I) := by
    cases hI : I with
    | zero => exact hu'_prim
    | succ J => exact hw_prim_all J
  have hmw : dot (expNormal (extChain d.toDecompData nℓ vl u' i I) vl)
      (extChain d.toDecompData nℓ vl u' i I) = 0 := Nivat.ColleReg.dot_expNormal_u'
  have hmvl : 0 < dot (expNormal (extChain d.toDecompData nℓ vl u' i I) vl) vl :=
    Nivat.LaneTowerPkg.dot_expNormal_pos hwvl_ne
  obtain ⟨b, hb⟩ := hBne
  have hb_cone : b ∈ coneRegion B vl u' := by
    rw [mem_coneRegion_iff]; exact ⟨b, hb, 0, 0, by simp⟩
  have hb_I : b ∈ tower (coneRegion B vl u') (wtower d.toDecompData nℓ vl u' i) I :=
    tower_monotone _ _ (Nat.zero_le I) hb_cone
  have hb_Rinf : b ∈ tower (coneRegion B vl u') (wtower d.toDecompData nℓ vl u' i) (I + 1) :=
    tower_subset_succ _ _ I hb_I
  have hstep_neg : dot (expNormal (extChain d.toDecompData nℓ vl u' i I) vl)
      (wtower d.toDecompData nℓ vl u' i I) < 0 :=
    dot_m_step_neg d.toDecompData hvl_prim hprim hperp henv i hdoth hadjB hunimod hnu' hnℓ_ne hIlen
  have hunb : ∀ bb : ℤ, ∃ z ∈ tower (coneRegion B vl u') (wtower d.toDecompData nℓ vl u' i) (I + 1),
      dot (expNormal (extChain d.toDecompData nℓ vl u' i I) vl) z < bb :=
    fun bb => hunb_of_sweep_neg hb_I hstep_neg bb
  have htop : ∃ top : ℤ, ∀ z ∈ tower (coneRegion B vl u') (wtower d.toDecompData nℓ vl u' i) (I + 1),
      dot nℓ z ≤ top := by
    refine Nivat.HsuppTowerBase.dot_le_of_mem_tower_bounded hBfin (le_of_eq hperp) (by omega)
      (wtower d.toDecompData nℓ vl u' i) (I + 1) ?_
    intro k hk
    by_cases hklen : k < (sortedCand d.toDecompData nℓ u' i).length
    · exact le_of_lt (dot_of_mem_candSet d.toDecompData hvl_prim hprim hperp i hdoth
        (mem_candSet_wtower hklen))
    · have heq : wtower d.toDecompData nℓ vl u' i k = -vl := by
        simp only [wtower]; rw [dif_neg hklen]
      rw [heq, dot_neg_right_loc, hperp]
      norm_num
  have hR : Colle41.IsRegion (tower (coneRegion B vl u') (wtower d.toDecompData nℓ vl u' i) (I + 1)) vl
      (extChain d.toDecompData nℓ vl u' i I) := by
    refine ⟨hconvAll (I + 1) (by omega), ⟨b, rayIn_tower_vl _ (I + 1) hb_Rinf⟩, ⟨b, ?_⟩⟩
    exact rayIn_tower_extChain d.toDecompData i I hb_cone
  classical
  have hFne : (hBfin.toFinset).Nonempty := ⟨b, hBfin.mem_toFinset.mpr hb⟩
  obtain ⟨bmax, hbmaxF, hbmax_ge⟩ := hBfin.toFinset.exists_max_image
    (fun x => dot (expNormal (extChain d.toDecompData nℓ vl u' i I) vl) x) hFne
  have hbmax_B : bmax ∈ B := hBfin.mem_toFinset.mp hbmaxF
  have hbmax_cone : bmax ∈ coneRegion B vl u' := by
    rw [mem_coneRegion_iff]; exact ⟨bmax, hbmax_B, 0, 0, by simp⟩
  have hbmax_I : bmax ∈ tower (coneRegion B vl u') (wtower d.toDecompData nℓ vl u' i) I :=
    tower_monotone _ _ (Nat.zero_le I) hbmax_cone
  have hseed : ∀ b' ∈ B, dot (expNormal (extChain d.toDecompData nℓ vl u' i I) vl) b' ≤
      dot (expNormal (extChain d.toDecompData nℓ vl u' i I) vl) bmax :=
    fun b' hb' => hbmax_ge b' (hBfin.mem_toFinset.mpr hb')
  obtain ⟨hcutsub, hroom⟩ := tower_room d hvl_prim hprim hperp henv hBfin i hdoth hadjB hdetu hnu'
    hnl hIlen hconvAll
  refine ⟨tower (coneRegion B vl u') (wtower d.toDecompData nℓ vl u' i) (I + 1),
    extChain d.toDecompData nℓ vl u' i I, hdet, hw_prim,
    expNormal (extChain d.toDecompData nℓ vl u' i I) vl, hmw, hmvl,
    dot (expNormal (extChain d.toDecompData nℓ vl u' i I) vl) bmax, hR,
    ⟨bmax, tower_subset_succ _ _ I hbmax_I, rfl⟩, hunb, ?_, hnper, hwneg, htop, ⟨I, hIlen, rfl⟩,
    ⟨_, ?_, hroom⟩⟩
  · intro lev hlev0
    refine PeriodOn.mono ?_ hper
    intro z hz
    have hstepAll : ∀ J : ℕ, J ≤ (sortedCand d.toDecompData nℓ u' i).length →
        dot (expNormal (extChain d.toDecompData nℓ vl u' i J) vl)
          (wtower d.toDecompData nℓ vl u' i J) < 0 :=
      fun J hJ => dot_m_step_neg d.toDecompData hvl_prim hprim hperp henv i hdoth hadjB hunimod
        hnu' hnℓ_ne hJ
    exact Nivat.TowerHBaseMin.hcut_tower d.toDecompData hBfin ⟨b, hb⟩ hvl_prim hprim hperp i hdoth
      hnu hconvAll hstepAll I hIlen _ hseed z hz.1 (by rw [← hlev0]; exact hz.2)
  · intro lev n hL0
    refine PeriodOn.mono ?_ hper
    intro z hz
    exact hcutsub z hz.1 (le_trans hL0 hz.2)

end Package

end Hole2Room

/-- 2026-09-22：`exists_cutResidualR_of_claim46` 的 14 个 binder 级 `sorry` 按生产者分组收成
**三个**，每个恰对应一条 lane 的交付物（接口契约：结论逐字符 = 这里的 `obtain` 语句）：
塔（`:806-820`）/ 放置（`:822-852`，`v τ ε` 在 `lev` 之后选）/ 覆盖（`:848-856`）。
生成集 `Sφ a hgen` 由 `L1GenPackage.exists_gen_package` 供给（已落地）。 -/
theorem exists_cutResidualR_of_claim46
    {e : ℤ × ℤ} (hξ : IsMinimalCounterexample ξ) (d : DecompDataZ ξ)
    (hgen : Nivat.Colle.GeneratesAt ξ S gen)
    {B : Set (ℤ × ℤ)} {u' nℓ : ℤ × ℤ} {c : ℤ}
    (henv : Nivat.LE2.EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) B)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hvl_prim : Primitive vl) (hc : 0 < c)
    (hperp : Nivat.LE2.dot nℓ vl = 0)
    -- 2026-09-24（第 182 轮，集成者）：**`hdetpos` 是在调用点免费的定向，不是新债。**
    -- 唯一项级调用点（本文件 `exists_cutResidualR` 末尾）的 `nℓ` 由
    -- `LineGenIndex.exists_nℓ_and_index_of_oneSided` 产出，那条结论的三个合取
    -- （`Prim nℓ` / `dot nℓ vl = 0` / `dot nℓ (h i) = 0`）**在 `nℓ ↦ -nℓ` 下逐条不变**，
    -- 而 `det nℓ vl ≠ 0`（`det_ne_zero_of_dot_eq_zero`，本文件，输入只有 `nℓ ≠ 0`、
    -- `vl ≠ 0`、`hperp`），所以在**生产者一侧**做一次符号归一即可交出这一条——见调用点那条
    -- `obtain` 的证明。这正是 `PROTOCOL.md` §54 下半的「状态 2」：输入与输出都对
    -- `τ : nℓ ↦ -nℓ` 不变 ⟹ 生产者免费归一，**不许**因此去改消费者的分支结构。
    -- ⚠ 本条目前在本定理**体内**尚无消费者，它是给下面那个 `hstrict` 的 `sorry` 用的
    -- （`hstrict` 要在 `nℓ` 的定向上说话）。归一化字典**已落地主仓**：
    -- 〔2026-09-26 订正：`hstrict` 已删；本条现在的体内消费者是塔包 `Hole2Room.package_room`，
    --  经 `RegionNlDict.nl_eq_neg_dir_vl_and_det_u'` 钉死 `det u' vl = -1`（`towerIdx` 正向支）。〕
    -- `Nivat.RegionNlDict.nl_eq_neg_dir_vl_and_det_u'` / `unimod_of_normalized` /
    -- `prim_nl_of_normalized`（`RegionNlDict.lean`，第 183 轮，公理全白）。
    -- ⛔ **但「把 `hunimod`（`:1906`）与 `hprim`（`:1929`）降级成推论」暂缓**
    -- （2026-09-24 裁决，集成者）：这两条的下游是 `hwadj`，而本轮已判定
    -- `hwadj ⟺ ℓ_I 与 ℓ 扇相邻 ⟺ I 在方向表末端`、且 `I = len` 在
    -- `exists_tower_index` 现签名下推不出（规矩 17 的原文转录未回）。给一个
    -- 还造不出来的东西减前提，只会让签名再漂一次。等转录结论回来一次定。
    -- 原文对应：`b3_colle2.txt:774`
    -- 的 `ℓ` 与 `v⃗_ℓ` 的定向约定（`NOTATION.md` 的 `vl = dir nℓ` 条）。
    (hdetpos : 0 < det nℓ vl) (hnu : Nivat.LE2.dot nℓ u' = -1)
    (hbase₁ : Nivat.Colle41.PeriodOn (T e ξ)
      (Nivat.ConeRegion.coneRegion B vl u') (c • vl))
    -- 2026-09-22（集成者，lane-tower 发现）：塔的方向序列要从 `𝒮_φ` 的生成元构造（`:808`），
    -- 需要知道哪个生成元平行于 `vl`（Lemma 2.6，`i`/`hdoth`）和 `u'` 与 `vl` 之间没有 `𝒮_φ`
    -- 的边法向（`:764` 的相邻性，`hadj`）。这三条在调用点 `exists_cutResidualR` 里本来就在
    -- 作用域（`:2634`/`:2646`），只是没有传下来；这里补成 binder，纯接线。
    (hprim : Nivat.LE2.Prim nℓ) (i : Fin d.toDecompData.m)
    (hdoth : Nivat.LE2.dot nℓ (d.toDecompData.h i) = 0)
    (hadj : ∀ n ∈ Nivat.LE2.E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)),
      ¬ (Nivat.LE2.dot n vl < 0 ∧ 0 < Nivat.LE2.dot n u')) :
    Nonempty (L1Claim.CutResidualR ξ S vl) := by
  -- 塔包（lane-tower2）：原文 `:806-820`。塔以 `𝒮_φ` 的边方向循环序扫掠（`:808`），最后一个方向
  -- `ℓ_{ι−m} = −ℓ`（`:810`），使塔顶含半平面、经 Prop 2.12
  -- （`HalfPlaneNotPeriodOn.not_periodOn_of_halfPlane_subset`）不周期；`I` 由
  -- `TowerIndex.exists_last_periodOn_finite` 取；`Rinf := 𝓡_{I−1}`；**`w := v⃗_{ℓ_I}`**（`:816` 的 `ℓ'`），
  -- `m ⟂ w`；`b₀` 是 `ℓ'_{𝓡_I}` 支撑线的 `m`-高度，于是 `cut Rinf m lev 0 = 𝓡_I`（`:818` 的 `d_0 = 0`）。
  -- 2026-09-22 追加两条（覆盖包需要，原文 `:386-400` 的 `(−ℓ, ℓ')`-区域有两条半无限边，
  -- `−ℓ` 那条就是 `nℓ` 方向的上界）：`dot nℓ w < 0`、`Rinf` 在 `nℓ` 方向有上界。
  -- **2026-09-23（第一百五十一轮）：`hroomT` 已从本 `obtain` 删除。**  它曾是第 11 条合取
  -- （「gap 点加上 `𝒮_φ − a` 的上半部分仍在 `Rinf`」）。两条内核见证否掉了它作为塔包合取的资格：
  -- * 整行版（`∀ p ∈ Rinf, dot m p < b₀ → …`）本身为假（`tmp/wip/lane-hroomT-counterexample.lean`）。
  -- * 射线族版也救不回来：塔包这一点上 `lev/N/Sφ/a/v/τ/ε/g/t₀` 全都还没引入（分别在下面
  --   `:1758`/`:1764`/`:1778`/`:1826` 才出现），所以塔包只能对 `g,τ,t₀,L` 全称量化；而
  --   `Nivat.ColleReg.rayRoomSig_imp_hroomTSigWeak`（`tmp/wip/lane-B-roomray.lean`）证明取
  --   `g := p, τ := 0, t₀ := 1, k := 0` 就把射线族版塌回整行版，因而同样为假。
  -- 结论：这条「房间」事实不是与窗口无关的抽象几何事实，必须在 `hcover` 现场、用 `g ∈ S.image (· + v)`
  -- 的真实来源约束（`hline`/`hedge`）就地兑现——那正是 Claim 4.7（`b3_colle2.txt:824-856`）的几何内容。
  -- 债务已下移到本证明里 `have hroom` 处。`OPEN.md` #13。
  obtain ⟨Rinf, w, hw_det, hw_prim, m, hmw, hmvl, b₀, hR, h0, hunb, hbase, hinf, hwneg,
      htop, hwid, L0, hperL0, hroomBelow⟩ :
      ∃ (Rinf : Set (ℤ × ℤ)) (w : ℤ × ℤ), det vl w ≠ 0 ∧ Primitive w ∧
        ∃ (m : ℤ × ℤ), Nivat.LE2.dot m w = 0 ∧ 0 < Nivat.LE2.dot m vl ∧
        ∃ (b₀ : ℤ), Colle41.IsRegion Rinf vl w ∧
        (∃ z ∈ Rinf, Nivat.LE2.dot m z = b₀) ∧
        (∀ b : ℤ, ∃ z ∈ Rinf, Nivat.LE2.dot m z < b) ∧
        (∀ lev : ℕ → ℤ, lev 0 = b₀ →
          Nivat.Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev 0) (c • vl)) ∧
        ¬ Nivat.Colle41.PeriodOn (T e ξ) Rinf (c • vl) ∧
        Nivat.LE2.dot nℓ w < 0 ∧ (∃ top : ℤ, ∀ z ∈ Rinf, Nivat.LE2.dot nℓ z ≤ top) ∧
        (∃ I : ℕ, I ≤ (sortedCand d.toDecompData nℓ u' i).length ∧
          w = extChain d.toDecompData nℓ vl u' i I) ∧
        -- 2026-09-26（hole2-ctx）：第 13 条合取 ＝ `Hole2Room.tower_room`。`L0` 以上的 cut 都在
        -- `tower I` 里（故周期）；`L0` 以下有整块 `𝒮_φ − a` 的房间。见本文件 `namespace Hole2Room`。
        (∃ L0 : ℤ,
          (∀ lev : ℕ → ℤ, ∀ n : ℕ, L0 ≤ lev n →
            Nivat.Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev n) (c • vl)) ∧
          (∀ a ∈ d.toDecompData.Sphi,
            (∀ b ∈ d.toDecompData.Sphi, Nivat.LE2.dot m a ≤ Nivat.LE2.dot m b) →
            (∀ b ∈ d.toDecompData.Sphi, Nivat.LE2.dot m b = Nivat.LE2.dot m a →
              ∃ t : ℕ, b = a + (t : ℤ) • w) →
            ∀ P ∈ Rinf, Nivat.LE2.dot m P < L0 →
              ∀ b ∈ d.toDecompData.Sphi, P + (b - a) ∈ Rinf)) :=
    -- 2026-09-23（第一百五十七轮）：塔包落地，本条 `sorry` 清零。见上方 import 处的说明。
    -- 2026-09-24（第 195 轮）：第 12 条合取**追加**——塔包挑的 `w` 的**身份**
    -- （`w = extChain … I`，`I ≤ len`）。原先十一条只说 `w` 的符号性质，`w := extChain … I`
    -- （`TowerPkgMain.lean:951`）被 `∃ w` 吞掉，任何关于「`w` 选得对不对」的推理都接不上
    -- （lane-env-refute 第 194 轮亲读 `TowerPkgMain.lean:1024-1046` 发现）。
    -- ⚠ 这条**不承诺 `I` 等于几**：第 195 轮已判定塔的索引字典（`Ilean ↔ I_paper` 的平移方向）
    -- 尚未数值验证，见 `CORE-HOLES.md` 第 195 轮订正 F4。此处只导出存在性，定向无关。
    -- 2026-09-26：换成 `Hole2Room.package_room`（前 12 条与 `lane_towerpkg_package_wid` 逐字符
    -- 相同，多吃一个本声明现成的 `hdetpos`），仍然不承诺 `I` 等于几。
    Hole2Room.package_room hξ d henv hBfin hBne hunimod hvl_prim hc hperp hdetpos
      hnu hbase₁ hprim i hdoth hadj
  -- 2026-09-22：`lev` 改用相邻版（原文 `:816` 的 `d_n` 枚举**所有**被取到的距离），多出
  -- `hconsec`，使 `cut (N+1) \ cut N` 恰是一条 `w`-行（`:818`）。
  obtain ⟨lev, hlev0, hlev, hexh, hgap, hconsec⟩ :=
    Nivat.CutLevels.exists_lev_consecutive h0 hunb
  -- 生成包（lane-leafa，2026-09-22 落地）：`a` 取字典序极值（先 `dot m` 极小，同层再按 `w` 方向
  -- 极小），`Sφ.erase a` 格凸由该极值的唯一性给出（仿 `exists_vertex_of_generating` 的凸包外证法，
  -- 换成极小值 + `m`/`w` 组合的线性泛函）；同层点相差 `w` 的整数倍由
  -- `det_eq_zero_of_dot_eq_zero` + `exists_smul_of_det_eq_zero` 得出。见 `L1GenPackage.lean`。
  obtain ⟨Sφ, a, hgenφ, hSφ, ha_min, ha_end⟩ :
      ∃ (Sφ : Finset (ℤ × ℤ)) (a : ℤ × ℤ), Nivat.Colle.GeneratesAt ξ Sφ a ∧
        Sφ = d.toDecompData.Sphi ∧
        (∀ b ∈ Sφ, Nivat.LE2.dot m a ≤ Nivat.LE2.dot m b) ∧
        (∀ b ∈ Sφ, Nivat.LE2.dot m b = Nivat.LE2.dot m a → ∃ t : ℕ, b = a + (t : ℤ) • w) :=
    Nivat.L1GenPackage.exists_gen_package' d hmw hw_prim hmvl
  -- 放置包（lane-place，2026-09-22 扩展落地）：原文 `:822-852`，沿 `v⃗_{ℓ'} = w` 放置，
  -- `v τ ε` 在 `lev` 之后选。`exists_line_package'` 一次性产出 `hline ∧ hedge`：`hedge` 用
  -- `hconsec` 把 `hgap` 的区间钉死成等式（gap 行的 `dot m` 高度恰为 `lev (N₀+1)`），再用
  -- `recession_of_ray`（任意点起都封闭）把 `vl`-射线与 `w`-射线同锚在 gap 行的一点 `z_gap`，
  -- `lattice_pt_of_cone_mem` 的双射线锥退化为单顶点锥，给出 `S` 的整条窗口在 `Rinf` 里的
  -- 平移 `v`；顶面（`dot m`-极小的 argmin，用 `L1EdgeFace.lean` 的 `topFace_*_eq_argmin`
  -- 按 `m = lam • perp w` 的符号选 `ε`）恰好卡在 `lev (N₀+1)` 上，非顶面严格更高。
  -- 见 `L1LineEdgePackage.lean`。
  obtain ⟨v, τ, ε, hcombined⟩ :
      ∃ (v : ℤ × ℤ) (τ : ℤ) (ε : Bool), ∀ (N : ℕ),
        Nivat.Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev N) (c • vl) →
        ¬ Nivat.Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev (N + 1)) (c • vl) →
        (∀ z ∈ L1Data.derivedQ ε w (S.image (· + v)),
          τ • w + z ∈ Nivat.L1Region.cut Rinf m lev N ∧
          τ • w + z + c • vl ∈ Nivat.L1Region.cut Rinf m lev N) ∧
        (∀ z ∈ S.image (· + v), z ∉ L1Data.derivedQ ε w (S.image (· + v)) →
          τ • w + z ∈ Nivat.L1Region.cut Rinf m lev (N + 1) ∧
          τ • w + z ∉ Nivat.L1Region.cut Rinf m lev N) :=
    Nivat.L1LinePackage.exists_line_package' (e := e) (c := c) (S := S) Rinf w hw_det hw_prim
      m hmw hmvl lev b₀ hlev0 hlev hexh hgap hconsec hR hc hvl_prim hinf
  have hline : ∀ (N : ℕ),
      Nivat.Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev N) (c • vl) →
      ¬ Nivat.Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev (N + 1)) (c • vl) →
      ∀ z ∈ L1Data.derivedQ ε w (S.image (· + v)),
        τ • w + z ∈ Nivat.L1Region.cut Rinf m lev N ∧
        τ • w + z + c • vl ∈ Nivat.L1Region.cut Rinf m lev N :=
    fun N h1 h2 => (hcombined N h1 h2).1
  -- 消费者只在 `hcover` 处用它，不进 `CutResidualR` 结构。生产者：lane-place（放置包）。
  have hedge : ∀ (N : ℕ),
      Nivat.Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev N) (c • vl) →
      ¬ Nivat.Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev (N + 1)) (c • vl) →
      ∀ z ∈ S.image (· + v), z ∉ L1Data.derivedQ ε w (S.image (· + v)) →
        τ • w + z ∈ Nivat.L1Region.cut Rinf m lev (N + 1) ∧
        τ • w + z ∉ Nivat.L1Region.cut Rinf m lev N :=
    fun N h1 h2 => (hcombined N h1 h2).2
  -- 覆盖包（lane-l1-cover）：原文 `:848-856`，Figure 11(B)，射线沿 `w`。
  -- 覆盖包接线（lane-chain，2026-09-22）：`hcover_of_hedge`（`L1CoverBridge.lean`）从
  -- `hedge` 的占位点桥接到 Figure 11(B) 的截断枚举覆盖；仍欠 `hstep_all`
  -- （原文 `:848-856` 的真正几何窗口步进内容，`Sφ.erase a` 组合），未证。
  have hm0 : m ≠ 0 := fun h => by simp [h, Nivat.LE2.dot] at hmvl
  have hray_vl : ∀ z ∈ Rinf, z + vl ∈ Rinf := by
    obtain ⟨z₀, hrayvl⟩ := hR.2.1
    exact Nivat.RecessionCone.recession_of_ray hR.1 hrayvl
  have hRinf' : ∀ z ∈ Rinf, z + c • vl ∈ Rinf := by
    intro z hz
    have hcnat : (c.toNat : ℤ) = c := Int.toNat_of_nonneg hc.le
    have hstepc := Nivat.L1CoverPackage.add_nsmul_mem hray_vl z hz c.toNat
    rwa [hcnat] at hstepc
  have hcover : ∀ (N : ℕ),
      Nivat.Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev N) (c • vl) →
      ¬ Nivat.Colle41.PeriodOn (T e ξ) (Nivat.L1Region.cut Rinf m lev (N + 1)) (c • vl) →
      ∀ g ∈ S.image (· + v), g ∉ L1Data.derivedQ ε w (S.image (· + v)) → ∀ t₀ : ℤ, τ ≤ t₀ →
        Nivat.L1StraddleMax.overlap (Nivat.L1Region.cut Rinf m lev (N + 1)) (c • vl) ⊆
          Nivat.MaxEnv.genClosure Sφ a
            (Nivat.L1StraddleMax.overlap (Nivat.L1Region.cut Rinf m lev N) (c • vl) ∪
              Nivat.L1StraddleMax.ray g w t₀) := by
    intro N h1 h2 g hgS hgD t₀ ht₀
    have hlev_mono : lev (N + 1) < lev N := by
      obtain ⟨z, hz, hz1, hz2⟩ := hgap N
      omega
    -- **Claim 4.7 的几何内容（`b3_colle2.txt:824-856`），第一百五十一轮从塔包下移到这里。**
    -- 原文 `:824` 把「房间」写成**挑选条件**（"for any translation `T` of `S` where
    -- `T \ ℓ'_T ⊂ R^N_I`, but `T ⊄ R^N_I`"），不是「任意放置都塞得下」。相应地这里的 `g` 也不是
    -- 任意格点：`hgS : g ∈ S.image (· + v)`、`hgD : g ∉ …`（`hline`/`hedge` 给的放置约束）。
    --
    -- **第一百五十二轮（口 B 定位）**：`hR` 的两条半无限边（`hR.2.1` 沿 `vl`、`hR.2.2` 沿 `w`）
    -- 经 `RecessionCone.room_of_cone`（`ConeRecession.lean:135`）张成整个实锥，把「房间」化归为
    -- `Sφ` 在角点 `a` 处的切锥被 `cone (vl, w)` 含住这一条纯有限命题。又因
    -- `dot m w = 0 < dot m vl`、`dot nℓ vl = 0 > dot nℓ w`，有
    -- `cone (vl, w) = {z | 0 ≤ dot m z ∧ dot nℓ z ≤ 0}`，而 `ha_min` 恰好给了前一半。
    -- **所以本 `sorry` 等价于「`a` 在 `Sφ` 上同时也是 `dot nℓ` 的最大点」。**
    --
    -- **第一百五十三轮（裁决，勿再走回头路）**：上一轮写在这里的下一步（「把
    -- `EnvOf ↑d.Sphi Rinf` 加进塔包 `obtain` 再用 `room_of_cone` 接」）**已被内核见证否掉**。
    -- 在 `tmp/wip/lane-hroom-hcone-refute.lean` 的实例（`vl=(0,1)`、`w=(-1,0)`、`m=(0,1)`、
    -- `nℓ=(1,0)`、`Rinf={z|z.1≤0}`、`Sφ` 为生成元 `(1,0),(1,1),(0,1)` 的 zonotope、`a=(1,0)`
    -- 由 `ha_min`+`ha_end` 唯一钉死）上：塔包的全部几何合取成立（`hR`/`h0`/`hunb`/`htop`/
    -- `hwneg`/…），而 `hcone` 与 `room_of_cone` 的结论为假（`not_hcone` / `not_room`）；
    -- 同一实例上 `tmp/wip/lane-env-refute-EnvRinf.lean:209` 证了
    -- `WeaklyEnveloped ↑Sφ Rinf` **成立**（`:233`/`:241` 打包），故包络合取救不回这里。
    -- 见证 `b = (2,1)`：`dot m (b-a) = 1 > 0` 而 `dot nℓ (b-a) = 1 > 0`，即 `a` 不是
    -- `dot nℓ`-最大点。机理是 `hcone` 真正要的是 `vl` 与 `w` 在 `Sφ` 的边方向循环序里于顶点 `a`
    -- 处**相邻**，这不是包络性能给的。（lane-B-roomray / lane-hroomT 更早已分别内核否掉整行版
    -- 与射线族版的抽象签名，连 `hgS`/`hgD` 都兑现过。）
    --
    -- **因此本 `sorry` 只能就地用 ξ-周期性关掉**（`hgen` / `hbase` / `hinf`），即原文
    -- `b3_colle2.txt:838-846` 那条「塞不进 `R^N_I` 时改走射线 `{g + t·v⃗_{ℓ'}}` ＋ η-生成」
    -- 的分支——我们从未形式化过它。`:824` 的挑选条件是**挑选条件**，不是普遍断言，
    -- 见 `blueprint/NOTE.md` 与 `OPEN.md` #13 / #13b。
    -- 见 `LANDING.md` 第一百五十二、一百五十三轮。
    --
    -- **2026-09-24 升级（第一百六十轮，`CORE-HOLES.md` / `OPEN.md #13`）：上面那条结论从
    -- 「`hcone` 这一条路走不通」升级成「整类走不通」。** 两份独立内核见证，集成者各自复核
    -- `check1.sh` EXIT=0、`#print axioms` 全白名单：
    --   * `Nivat.LaneTowerPkgGeomFalse.hole3_target_false_without_generation`
    --     （`tmp/wip/lane-towerpkg-hole3-geomfalse.lean:428`）兑现塔包 C 组 10 条 + B 组 7 条 +
    --     A 组 6 条共 23 条 binder，**只**去掉 `hξ` / `hgen` / `hgenφ`，并证明本 `have` 的下游
    --     结论 `hstep_all` 为假；
    --   * lane-env-refute 的 `not_hstep_all`（15 条 binder）同向。
    -- 合起来：**任何省掉 `hξ` / `hgen` / `hgenφ` 的引理都证不出 `hstep_all`。**
    -- ⚠ 这只证了**必要性**；「带上这三条就够」尚未证。
    -- 连带后果：`I < len`（`OPEN.md #12` 的二分问题）**不在本 `sorry` 的关键路径上**，
    -- 不要再往那个方向派工。
    -- 逐字符靶子已就位：`Nivat.LaneTowerPkgHroomSig.hroom_target`
    -- （`tmp/wip/lane-towerpkg-hroom-sig.lean:94`），binder 恰为本行作用域里现成的
    -- 48 显式 + 21 隐式，每条带引入行号；两道形状护栏经
    -- `Nivat.L1CoverPackage.step_all_of_hroom`（即下面 `:1925` 那个槽位）由内核判定。
    -- ── 2026-09-24（第 161 轮）：洞口从 48 binder 的一大坨缩成下面一行命题 ──
    -- `Nivat.Hole3Room.room_of_nlmax`（`Hole3Room.lean:292`，0 sorry、公理白名单）把本 `have`
    -- 的结论整条归约到 `hnlmax`，只吃 7 条现成前提：`hR.1`（格凸）、`hray_vl`（`:1868`）、
    -- `hwrec`（由 `hR.2.2` 经 `RecessionCone.recession_of_ray` 得）、`hw_det`、`hmw`、`hmvl`、
    -- `hperp`、`hwneg`。逐字符接线已由 `Nivat.LaneTowerPkgHroomNlmax.hroom_target_of_nlmax`
    -- （`tmp/wip/lane-towerpkg-hroom-nlmax.lean:110`，EXIT=0）在链外先行兑现过一遍。
    have hwrec : ∀ z ∈ Rinf, z + w ∈ Rinf := by
      obtain ⟨z₀', hrayw⟩ := hR.2.2
      exact Nivat.RecessionCone.recession_of_ray hR.1 hrayw
    -- **剩下的唯一缺口。** 原文 b3_colle2.txt:806-856（Figure 11(B) 的角点 `a`）：`a` 被取成
    -- `𝓡^N_I` 那个框的角点，因而在 `𝒮_φ` 上同时极小化 `dot m`（已有 `ha_min`）**和**极大化
    -- `dot nℓ`。逐量词对应：`∀ b ∈ Sφ` ↔「for every `b ∈ 𝒮_φ`」，`dot nℓ b ≤ dot nℓ a` ↔
    -- 「`b` 不在 `a` 的 `−ℓ` 一侧之外」。
    -- ⚠ 纯几何填不上（三条内核反例），**但每条的适用域都要读下面第 173 轮那一段**：
    --   * `hadj ⇏ hwadj`：`Nivat.LaneTowerPkgHadjNoWadj.hadj_does_not_imply_hwadj`
    --     （`tmp/wip/lane-towerpkg-hadj-nowadj.lean:218`）；
    --   * 去掉 `hξ`/`hgen`/`hbase`/`hinf` 后 `hnlmax` 为假：
    --     `Nivat.LaneEnvRefuteHadj.all_premises_and_not_nlmax`
    --     （`tmp/wip/lane-env-refute-Hadj.lean`，第 154 轮）；
    --   * 极小性本身也推不出 `hwadj`：`minimality_does_not_force_hwadj`
    --     （`tmp/wip/lane-env-refute-MinIdx.lean:273`）。
    -- 所以唯一活路是 ξ 那一侧（`hξ` / `hgen` / `hgenφ` / `hbase` / `hinf`）。
    --
    -- ── 2026-09-24（第 172/173 轮，集成者）：上面三条的**适用域**订正 ──
    -- 前两条都跑在 `SphiX`（`tmp/wip/lane-env-refute-Hadj.lean:93`）上，该实例 `vl=(0,1)`、
    -- `w=(-1,0)`，`vl` 与 `-w=(1,0)` 之间夹着边方向 `(1,1)` ⟹ **下标差 2**。
    -- 而原文的构型是**差 1**：`b3_colle2.txt:814` 逐字取「the **smallest** integer
    -- `ι−m+1 ≤ I ≤ ι−1` such that `(T^u η)|ℛ_I` is periodic of period `h`」，
    -- 且 `:876` **Claim 4.10 逐字「We have `I = ι−1`」**（已证定理），故 `s := ι − I = 1`，
    -- 与 `:760` 的 `ℓ' ∥ w_{ι−1}` 一致。⟹ 这两条**不是对原文构型的证伪**，
    -- 只说明「这组 binder 在差 2 的构型上不足以推出结论」。
    -- 反向的内核事实：`hwadj_wide`（`tmp/wip/lane-env-refute-MinIdx.lean:238`）里
    -- `vl` 与 `-w` 差 1 时 `hwadj` **成立**（那里 `vl` 与 `w` 隔 3 步，`m=4` 最远）。
    -- 根因是第 161/164/169 轮把 `hwadj` 的禁止锥从法向图景转述成方向图景时丢了负号：
    -- 正确的是 `cone(-w, vl)`，不是 `cone(vl, w)`。见 `NOTATION.md` 的 `E(·)` 跨侧一名两物条。
    -- ⟹ 洞 3 的改判：**不是原文为假，是塔包只导出纯符号事实、不含下标关系**；
    -- 缺的 binder 是「`-w` 与 `vl` 在 `E ↑𝒮_φ` 循环序里相邻」，桥 `nlmax_of_wadj`
    -- （`Hole3Room.lean`，同文件外引只写名字见 `PROTOCOL.md` §57；声明行 `:319`）现成。
    -- 第三条（`minimality_does_not_force_hwadj`）不受影响。
    --
    -- ── ⛔ 2026-09-24（第 185 轮，集成者）：上面那条「缺的 binder 是相邻性」**撤回**。
    -- **`hwadj` 不该被偿还，该被撤回。** 三条独立证据：
    --
    -- 1. **原文确实证了相邻性，但不在这里用。** lane-towerpkg 亲读 `b3_colle2.txt`：
    --    相邻性就是 **Claim 4.10**（`:876`「We have `I = ι-1`」，反证在 `:878`；Case 2 镜像
    --    是 Claim 4.15，`:926-928`）。原文次序是 Claim 4.6 `:780` → 选 `I` `:814` →
    --    `𝓡^n_I`/`N` `:818-820` → Claim 4.7 `:822` → `𝒦` `:860` → Claim 4.8 `:862` →
    --    Claim 4.9 `:868` → **Claim 4.10 `:876`** → 结论 `:880`。
    --    ⭐ **`I = ι-1` 只在 `:880` 被用一次**，从不参与 `𝓡^n_I` / `N` / `𝒦` /
    --    Claims 4.7–4.9 的构造。而我们把 `hwadj` 放在**区域构造的内部**（本 `have` 一带，
    --    喂 `Hole3Room.room_of_nlmax`）。⟹ 按原文次序，在这个位置上相邻性**还没有被证出来**；
    --    即使把 Lemma 4.4 整块转录完也不能在这里用，会循环。
    --    按硬规矩 5「先问哪个量词是我们加的」：`a` 早已判定是我们造的（见上，第 167 轮），
    --    **现在再加一条——要相邻性的那个位置也是我们自己选的。**
    --
    -- 2. **`hwadj` 在现签名下为假，不是「还没证」。** 两条独立见证，公理全白：
    --    lane-towerpkg 的 `w_ne_neg_u'`（`w = -u'` 与 `hnu`＋`dot nℓ w < 0` 冲突）与
    --    `not_hwadj_at_u'`（Claim 4.10 逼出的 `w = u'` 处，`3 ≤ d.m` 时 `hadj` 与 `hwadj`
    --    逼出 `det (h j) u' = 0` 对所有 `j ≠ i`，撞 `d.h_dir`）；
    --    lane-tower-hbase 的八边形台架（`hwadj ⟺ nℓ = 扇后继(νJ1)`，前提全合规而扇后继
    --    是 `(1,-1)` 不是 `nℓ`）。
    --
    -- 3. **债的源头是我们 2026-09-18 的一次删除。** 本文件 `:3973-3989` 逐字记着
    --    `case1_claim48_no_fully_periodic_acc` 被删，理由「it feeds his Claims 4.9/4.10 …
    --    not on our path」。那个判断对 `colle_region` 的**结论**成立，对 `hwadj` **不成立**：
    --    `hwadj` 恰恰是 Claims 4.8/4.9/4.10 的产物。
    --
    -- ⟹ 该撤的是 `hwadj`。**但「改用区域 ∪ 射线」这条后续路线同轮即被否掉**，见下。
    --
    -- ── ⛔ 2026-09-24（同轮稍后，集成者）：「把 `hroom` 换成 `Rinf ∪ 射线`」**撤回** ──
    -- 上面一度写过「该动的是 `hroom` 的形状，回到 `:838-846` 的区域 ∪ 射线」，并据此派了三条 lane。
    -- **那是错的，而且错得是算术级的**（lane-tower-hbase，premise-free，无台架，公理全白）：
    -- 1. **放宽结论集是空放宽。** 链上射线是 `L1StraddleMax.ray g w t₀`（方向 `w`），而塔包
    --    给 `hmw : dot m w = 0`（本文件 `:1857`）⟹ `dot m` 在整条射线上恒为 `dot m g`。
    --    而 `hroom` 的结论点 `Q := ((g + T•w) - k•w) + (b - a)` 在前提 `0 < dot m (b - a)` 下满足
    --    `dot m Q = dot m g + dot m (b - a) > dot m g` ⟹ **`Q` 恒不在射线上**
    --    （`room_conclusion_never_in_ray`）。把结论集换成 `Rinf ∪ ray` 与原版**逐字等价**
    --    （`room_ray_relaxation_is_vacuous`），一个字都没少要。
    -- 2. **放宽前提槽位是加强，更没用**（`widening_hyp_is_stronger`）。两个槽位都堵死。
    -- 3. **射线根本没被丢**：`hcover` 的结论集本来就带它——本文件 `:1891`
    --    `… ⊆ (overlap (cut Rinf m lev N) (c • vl) ∪ ray g w t₀)`。`hroom` 是覆盖证明**内部**的
    --    一个中间步，它不带射线不是转录遗漏，正是上面那条算术使然。
    -- ⟹ 连带作废：`hconv : IsLatticeConvexRegion (Rinf ∪ ray)` / `hvl` / `hw` 三条重证义务
    --    （原以为是 `RecessionCone.room_of_cone`（`ConeRecession.lean:135`）的代价）——**无人消费**。
    --    ⚠ **而且不可完成**（lane-towerpkg 2026-09-24，原文侧；补记以挡住「换个位置再提一次」）：
    --    并集的格凸性取决于射线起点 `t₀` 相对区域角点的位置，而原文对 `t₀` 的全部信息是
    --    `:826`（Claim 4.7 反证里的下标）与 `:844`（`g ∈ 𝒯 ∩ ℓ'_𝒯`），**都不约束这个相对位置**：
    --    同一份数据（`vl=(-2,1)`、`w=(1,0)`、`Rbad={z | 0 ≤ z.2 ∧ -2·z.2 ≤ z.1}`、`g=(0,-1)`）
    --    在 `t₀=0` 下 `hconv`/`hvl` **假**（失败点 `(-1,0)`），在 `t₀=2` 下三条**全真**——
    --    两种情形都与原文相容 ⟹ 推不出。`hw` 则是无条件白送的（`addW_knownSet`）。
    --    ⟹ 原文从不把这个并集称作区域：`:386`（Definition 3.1）把凸性写进区域的**定义**，
    --    `:816-818` 声明 `𝓡^n_I` 是区域，而 `:842`/`:846` 的并集**只**作限制域出现，
    --    `:848` 立刻用 `𝓡^{N+1}_I` 把它换回区域。**凸性只在两端，中间那个并集不承担它。**
    -- ⟹ 净结论：**`hroom` 已经不欠任何东西**，它下面一行就由 `Hole3Room.room_of_strict` 关掉。
    --    洞 3 的全部缺口收敛成唯一一条 `hstrict`（下方），而 `hstrict` 的语句里
    --    **既不含 `Rinf` 也不含射线**，只含 `Sφ` / `m` / `nℓ` / `a` / `b`。
    --    ⟹ 几何侧（区域形状、凸性、回收锥、相邻性）**全部出局**；剩下的只能走 ξ 那一侧。
    -- ⛔ 2026-09-24（第 195 轮，集成者）：**上面这三行的净结论已撤回**，保留是为了留痕。
    --    「`hroom` 不欠任何东西」只在「`hstrict` 可证」的前提下成立——它的证明体
    --    （下方 `room_of_strict … hstrict`）整条挂在 `hstrict` 上。而 `hstrict` 这条路线
    --    第 195 轮判为**走不通**（理由见下方 `hstrict` 处的三条腿）。⟹ `hroom` 一旦要绕开
    --    `hstrict`，就得先拆掉 `room_of_strict` 这条因式分解，那时它重新变成开着的目标。
    --    ⚠ 并且：`hroom` 的落点是 `∈ Rinf`，而原文 Figure 11(B)（`:856`）的机制要求落进
    --    **已知的** `𝓡^N_I ∪ 射线`；`:820` 的 `⋃_n 𝓡^n_I = 𝓡_{I−1} = Rinf` 说明 `Rinf`
    --    **弱得多** ⟹ **`hroom` 不是 (B) 的逐量词转写**（lane-towerpkg 第 195 轮对账，集成者采纳）。
    --    在读清 `L1CoverPackage.hcover_of_hedge` / `step_all_of_hroom` 到底要哪一条之前，
    --    不要把「债回到 `hroom`」当成已定靶子。
    --    📌 供给侧的独立佐证：`L1Region.isRegion_cut`（`L1Region.lean:202`，0 sorry、七处消费）
    --    已经把原文两个凸对象 `𝓡^N_I` / `𝓡^{N+1}_I`（＝链上 `cut Rinf m lev N` / `(N+1)`）
    --    的区域性从 `hR`/`hmw`/`hmvl` 白送掉了。且全树 `IsLatticeConvexRegion` **从未**施于任何
    --    `cut`（集成者 2026-09-24 全树 grep，零命中）⟹ 凸性义务在洞 3 这侧**是零**。

    --
    -- ── 2026-09-24（第 167 轮，集成者）：洞口砍掉一半 ──
    -- **`a` 不是原文的对象。** `b3_colle2.txt:806-870` 通篇没有引入任何点 `a`：那里只有
    -- `ℛ_i` / `ℛ^n_I` / `N` / `h` / `𝒯`，以及 Figure 11(B) 的传播论证（`:852`）。
    -- `a` 是我们自己在 `:1819-1826` 按**字典序极值**造的（先 `dot m` 极小，同层再按 `w` 极小）。
    -- 按硬规矩 5「先问哪个量词是我们加的」：三条内核反例之所以都成立，根就在这里——
    -- 不是几何证不出来，是「`a` 同时极大化 `dot nℓ`」这条要求本来就没有原文依据。
    --
    -- `ha_end`（极小层里的点全是 `a + t•w`，`t : ℕ`）+ `hwneg`（`dot nℓ w < 0`）⟹
    -- **`a` 在极小层上自动极大化 `dot nℓ`**，白送（`NlmaxReduce.nlmax_on_min_level`）。
    -- 又：`Hole3Room.room_of_nlmax` 的证明里 `hnlmax` **只在 `0 < dot m (b-a)` 的那个 `b`
    -- 上用了一次**，所以消费者侧本来就只要严格更高层那一半。两头一夹，洞口就是下面这条
    -- `hstrict`，直接喂给 `Hole3Room.room_of_strict`（`Hole3Room.lean:222`）。
    -- `NlmaxReduce.nlmax_of_strict` / `strict_of_nlmax`（`NlmaxReduce.lean:62`/`:80`）另证
    -- `hstrict` 与原来的 `hnlmax` 在现成前提下**等价**，故这次缩小没有丢信息。
    -- ══ 2026-09-26（hole2-ctx）：⛔ 这里原来是 `have hstrict : ∀ b ∈ Sφ, dot m a < dot m b →
    -- dot nℓ b ≤ dot nℓ a := by … sorry`。**已删除，不是被证出来的。** 理由（数值＋内核）：
    --   * `hstrict` ⟺ `I = len`（`CritIffTop.crit_iff_eq_top`，下面 (R1)）；
    --     `tmp/wip/hole2-corner-bench.py` 2439 个台架里 `hstrict` 恰在 `I = len` 的 586 个成立，
    --     其余全假 ⟹ 在塔包交付的一般 `I` 上它**不可证**（除非整个上下文空真）。
    --   * 它唯一的消费者 `hroom` 并不需要它：`hroom` 只在 `cut (N+1)` 不周期的那一行被调用，
    --     而塔包第 13 条合取（`Hole2Room.tower_room.1`）说 `L0` 以上的 cut 都周期 ⟹ 该行在 `L0`
    --     以下，那里 `Hole2Room.tower_room.2` 无条件给出房间（种子 `B` 的 `E(𝒮_φ)`-包络性，
    --     `HsuppContain.hcont`），见下面新的 `hroom` 证明。
    -- ⟹ 第 197 轮「`hstrict → hroom → 周期上推 → I = len → 判据 → hstrict`」的循环不是原文的，
    --   是 `room_of_strict` 那条 `∀ q ∈ Rinf` 因式分解造出来的；原文 `:848-856` 的房间来自
    --   `𝓡_{I-1}` 的 `ℓ_{I-1}`-边从种子角点出发，不来自 `a` 的角序极值。
    -- 以下保留原 `have` 体内的全部历史批注（第 192–225 轮），仅供留痕。
    -- ▸ 原 `have hstrict` 体：
      -- ── 2026-09-24（第 192 轮，集成者）：洞口再砍一刀，换成**纯判据** ──
      -- lane-tower-hlev 的 `hstrict_iff_det_gen_native`（`FanOrderCriterion.lean`，
      -- 公理全白；该文件每轮都在长，按第 193 轮口径只写标识符不写行号）把 `hstrict`
      -- **等价**换成扇形判据，且它的前提表逐条就在本作用域里：
      --   `hvl_prim`/`hperp`/`hdetpos`/`hnu` —— 本声明的原生 binder；
      --   `hw_prim`/`hwneg`/`hmw`/`hmvl`     —— 上面 `obtain`（塔包）的分量；
      --   `ha_min`/`ha_end`                  —— 上面 `obtain`（生成包）的分量；
      --   `ha : a ∈ Sφ`                      —— `GeneratesAt` 的第一个合取项
      --                                         （`Generating.lean:19` 逐字 `a ∈ S ∧ …`）。
      -- ⟹ 剩下的**唯一**缺口是下面那条判据，它已经不含 `ξ` / 周期性 / 凸性，纯粹是
      -- 「`w` 选得对不对」：每个生成元 `h j` 相对 `vl` 与 `w` 不得异侧。
      -- 第 193 轮：改走 `hstrict_of_det_gen_onsite`（`FanOrderCriterion.lean`，
      -- lane-tower-hlev 的 §11）。它保留 `Sφ` 与 `hSφ` 两个形参、结论也对 `Sφ` 说，
      -- 与本 `have` 的目标逐字符同形 ⟹ 现场三条 `rw [← hSφ]` 与一条 `rw [hSφ]`
      -- 全部消失，洞口一字不变（lane-env-refute 对抗性复核 F1）。
      -- （原 `refine Nivat.LaneTowerHlevFanOrder.hstrict_of_det_gen_onsite d … ?_`，已随 `have` 删除）
      -- **剩下的全部缺口**：塔包（`lane_towerpkg_package`，上面那条 `obtain`）挑的 `w`
      -- 必须让每个生成元都不被 `vl` 与 `w` 分到两侧。这条**推不出来，只能构造时挑对**：
      -- `dGZ` 台架上同一个 `d` 只换 `w`，本判据真假翻转（23 个合规 `w`，6 好 17 坏）。
      -- 兑现路线＝把塔包的结论加上这条合取项（前驱构造），见 `CORE-HOLES.md` 第 192 轮一节。
      --
      -- ⛔⛔ 2026-09-24（第 195 轮，集成者）：**上面这条兑现路线判为走不通。** 三条腿，
      -- 逐条标明证据等级（`PROTOCOL §50`：转引必须标「未独立验」）：
      --   **L1〔亲读〕** `hstrict_iff_det_gen_native`（`FanOrderCriterion.lean`）是 **`↔`**，
      --     不是充分路线；前提表逐条就是本作用域的原生 binder（即上面 `:2227-2231` 那张表），
      --     而 `hstrict_of_det_gen_onsite` 就是它的 `.mpr`。集成者与 lane-tower-hbase 各自独立亲读。
      --     ⟹ **判据 ⟺ 本 `have` 的目标**，两者同生共死。
      --   **L2〔转引，集成者未独立复核〕** 判据在 `extChain d nℓ vl u' i 0`（＝ `u'`，
      --     `TowerConstruct.lean` 的 `extChain` 零档）处**可证为假**
      --     （lane-tower-hbase `crit_at_u'_false` / `_bothsign`，后者两个定向分支都否）；
      --     在 `extChain … len` 处**无条件成立**（lane-towerpkg `hlast_good_discharge`）。
      --   **L3〔亲读＋裁决〕** 上面那条 `obtain` 的第 12 条合取只给 `∃ I ≤ len, w = extChain … I`，
      --     **不承诺 `I` 等于几**；`I` 的来源是 `ColleReg.exists_tower_index`（`TowerPackage.lean:308`，
      --     集成者当轮亲读）的结论 `∃ I, I < M ∧ PeriodOn (tower I) ∧ ¬ PeriodOn (tower (I+1))`
      --     ——**断裂点的存在量词，未钉值**。⟹ 要走通就必须另证 `I = len`；而原文 Claim 4.10
      --     （`b3_colle2.txt:876-878`，`I = ι−1`）说断裂发生在**近**端（＝沿后继序走了零步），
      --     恰是 `I = len` 的反面〔此读法来自 lane-hole3-cone 的原文转写，属裁决〕。
      -- ⟹ **关门理由不是「内核证明了本式在链上为假」**（那要先钉住 `I = 0`，没人证过），
      --    **而是**：本式等价于「`I = len`」，而原文给的是 `I = ι−1`。两头都堵：
      --    Claim 4.10 真 ⟹ 判据假；Claim 4.10 假 ⟹ 仍得另证 `I = len`，而那条线（`hper_len`）
      --    已因 `PROTOCOL §65`（原文最费力的前提 `hbase₁` 整条脱落）判红。
      -- ⟹ 这一格的**唯一**决定性问题回到 **Claim 4.10**（`:876-878`）。
      --
      -- ══ 2026-09-24（第 198 轮，集成者亲读原文）：破口 (D) 已答——**是同一个 `I`**，且上界承重 ══
      -- 问的是：`:876`（Claim 4.10）里的 `I`，和 `:814` 给出射程 `[ι−m+1, ι−1]` 的那个 `I`，是不是同一个。
      -- 〔等级：原文级，纯文本比对，无内核成分〕四条证据，最后一条是决定性的：
      --  1. `:814` 是 `I` 的**唯一**引入处：「we may consider the smallest integer `ι−m+1 ≤ I ≤ ι−1`
      --     such that `(T^u η)|R_I` is periodic of period `h`」。全篇再无第二处定义 `I`。
      --  2. `:816` 紧接着「we will write `ℓ_I = ℓ'`」⟹ Claims 4.8/4.9 全程的 `ℓ'` 就是这个 `I`。
      --  3. `:818` 的 `R^n_I` 由 `R_I` 造，`:860` 的 `𝒦 ⊂ R^N_I`，`:878` 又写「the `(−ℓ, ℓ_I)`-region `𝒦`」
      --     ——`:814 → :816 → :818 → :860 → :878` 一条未断的引用链，中间没有换过 `I`。
      --  4. ⭐ **决定性**：`:878` 的证法是「suppose, by contradiction, that `I < ι−1`」——
      --     **只反证 `<`，不反证 `>`**。而只有带上 `:814` 的上界 `I ≤ ι−1`，「非 `= ι−1`」才等价于「`< ι−1`」。
      --     ⟹ Claim 4.10 的证明**实际使用**了 `:814` 的射程 ⟹ 两处的 `I` 必须是同一个，否则该证明不完整。
      -- ⟹ (D) 关闭：同一个 `I`，且 `:814` 的上界是 Claim 4.10 证明的承重前提，不是装饰。
      -- ⚠ 这**不**放松顺序禁令：`:860` 的 `𝒦` 来自 Claim 4.7 + Lemma 4.1，`:878` 用 `𝒦`
      --    ⟹ Claim 4.10 仍在 Claim 4.7 **下游**，而 `hstrict` 在 Claim 4.7 的消解里。
      --    Claim 4.10 永远不许当 binder 来证 `hstrict`——(D) 的结论只用于**读懂**上面 L3 的对立面，
      --    即「原文的 `I = ι−1` 确实与我们要的 `I = len` 是同一个量的两个取值」，两头堵的判读因此坐实。
      --
      -- ══ 2026-09-24（第 196 轮，集成者）：上面那个「唯一决定性问题」已答，判据路线**确定关门** ══
      -- 三条理由互相独立，逐条标等级（`PROTOCOL §50`）：
      --
      --  **(R1)〔内核〕L2 升级：判据沿 `I` 单调，且阈值就是 `len`。**
      --    lane-tower-hbase `crit_mono_extChain` / `crit_threshold_extChain` /
      --    `crit_false_below_top` / `crit_iff_eq_top`（`tmp/wip/lane-tower-hbase-idxdict.lean` §11–§12，
      --    `check1.sh` EXIT=0，公理全白）。机理：判据 `det (h j) vl * det (h j) w ≤ 0` 逐字＝
      --    「直线 `±h j` 落在 `vl` 到 `w` 的闭扇形里」；链上每档都在 `vl` 的同一开半平面
      --    （`dot_extChain_neg`）且角度沿 `I` 严格递增（`det_pos_extChain`）⟹ 扇形嵌套扩大
      --    ⟹ 判据向上封闭。阈值 `= len` 因为链顶那档**本身就是某个生成元方向**
      --    （`mem_candSet_wtower`，`TowerConstruct.lean:402`），喂给它自己当场破。
      --    ⟹ 第 195 轮写的「L2 只否掉 `I = 0` 一个实例」作废：**`0 ≤ I < len` 全档为假**，
      --    且 `crit_false_below_top` 连 `hlast` 都不吃。⟹ 判据路线 ⟺ `I = len`，不多不少。
      --
      --  **(R2)〔原文转写＋裁决〕链上交付的 `I` 是 `0`，不是 `len`。**
      --    词典：`:806` 逐字 `𝓡_i := {g + t v⃗_{ℓ_i} : g ∈ 𝓡_{i+1}, t ∈ ℤ₊}`（`ι−m+1 ≤ i ≤ ι−2`）
      --    ⟹ 递推**从 `𝓡_{i+1}` 造 `𝓡_i`**，下标递减方向增长；种子 `𝓡_{ι−1}`（`:804`，周期）。
      --    链上 `tower 0 = coneRegion B vl u'`，`tower (n+1) = sweep (tower n) (w n)` ⟹
      --      **`tower n = 𝓡_{ι−1−n}`**。
      --    三处佐证：`:812` 的 `𝓡_{ι−1} ⊂ ⋯ ⊂ 𝓡_{ι−m+1}` 与 `tower_strict_chain` 同向；
      --    `:810` 塔顶含半平面 ⟹ 不周期，对上 lane-env-refute 内核台架 `tower3_is_halfPlane`；
      --    下标范围 `n = ι−1−i ∈ [0, m−2]` 与 `len = |sortedCand| ≤ m−1` 相容。
      --    极值方向自洽：原文 `I` ＝**最小**下标使 `𝓡_I` 周期；下标小 ⟹ 区域大 ⟹
      --    ＝**最大**的仍周期的区域 ＝ `exists_tower_index` 给的那个最大 `n`。⟹ `I_lean = ι−1−I_paper`。
      --    Claim 4.10（`:876` 逐字 `We have I = ι−1.`，lane-hole3-cone 当轮亲读，`I=ι−1` 是**结论**
      --    不是前提）⟹ **`I_lean = 0`**。配 (R1) 的 `crit_threshold_pos`（`1 ≤ I★ = len`）⟹
      --    `0 ≠ len` ⟹ **判据在链上交付的那个 `I` 处为假**。
      --
      --  **(R3)〔原文，逐字复核〕结构性理由，不依赖 `I` 取值、也不依赖 Claim 4.10 真假。**
      --    原文通篇 `:775-884` **没有**给 `ℓ'` / `ℓ_I` 任何角序／极值刻画——`I` 的唯一定义依据是
      --    `:814` 的「周期性在哪断」（lane-hole3-cone 逐句复核两轮，按 `§51` 报「找不到就是找不到」）。
      --    而判据是纯**角**条件（由 (R1) 的机理，等价于 `cone(vl,w)` 含住 `Sφ` 全部 `2m` 条边方向，
      --    `:319`）。⟹ **原文里没有任何机制能把「周期性断裂点」和「角序极值」连起来。**
      --
      -- ⟹ ⛔ **不要再往判据路线投入。** 兑现路线（把这条合取项加进塔包的构造）正式作废。
      --    ⚠ 措辞按 `§50`：(R1) 是内核，(R2)(R3) 是原文＋裁决（Claim 4.10 未形式化）⟹
      --    对外说「不要再投入」，**不说**「内核证明了本式为假」。
      --
      -- ⟹ 那么 `hstrict` 还剩什么路？由 L1 的 `↔`，`hstrict` 与判据同生共死 ⟹ **没有第二条来路**，
      --    除非经 `hξ : IsMinimalCounterexample ξ`（lane-env-refute 第 196 轮用**满前提**内核反例
      --    `newTarget_false` 否掉了不经 `hξ` 的 `hadj` 路线：根因是 `hadj` 禁 `0 < dot n u'`、
      --    `hwadj` 禁 `dot n w < 0`，**是相反的一侧**，互不蕴含）。而 lane-hole3-cone 查证
      --    Theorem 1.15 的证明段（`§4.2`，`:762` 起）**一次都没用极小性**（那是 Theorem 1.12 的手法，
      --    `:230`）〔此条标未验：只核了原文侧，未反查链上 `hξ` 的用法〕。
      -- ⟹ **`hstrict` 这个因式分解本身不是原文的东西**（跟 `a` 一样是我们造的，见上方第 167 轮一节）。
      --    下一步的靶子是 `hroom` 本身，而**不是**继续找 `hstrict` 的证法。见下方 `hroom` 处的新一节。
      --
      -- ══ 2026-09-24（第 197 轮，集成者）：⚠ **上面第 196 轮的 (R3) 撤回；本格重开为「一个 bit」** ══
      --
      -- 第 196 轮我用三条理由关判据路线，其中 (R3) 是「原文 `:775-884` 没给 `ℓ'`/`ℓ_I` 任何角序或
      -- 极值刻画，故没有机制能把周期断裂点连到角序极值」。**这条是错的，撤回。**
      --
      -- (a) 撤回的依据（lane-hole3-cone 找到、lane-towerpkg 与集成者各自亲读复核）：
      --     `b3_colle2.txt:764` 逐字给出 `2m` 条**有向**线 ↔ `𝒮_φ` 的 `2m` 条边的双射
      --     （定冠词＋单数＋successor 结构；紧接的下一句 "either parallel or antiparallel"
      --     证明这里是有向读法）。配 Claim 4.10（`:876`「We have `I = ι−1`」）⟹ `ℓ' = ℓ_{ι−1}`
      --     与 `ℓ = ℓ_ι` 在环序里**相邻**。**这就是一条角序刻画。**
      --     ⚠⚠ **第 199 轮：(a) 的原文侧仍成立，但它接到链上的那一步塌了。** `:764` 的双射、
      --        `:876` 的 `I = ι−1`、以及「`ℓ_{ι−1}` 与 `ℓ_ι` 环序相邻」这三件都是原文侧事实，不动。
      --        塌的是**把它搬到链上**所用的字典：lane-towerpkg 报假 (u3)（`coneRegion B vl u' ≅ 𝓡_{ι−1}`），
      --        链侧 `det u' vl = -1`（恒等式 `dot nℓ x = det x vl`，`hnu` 逐字就是它）与原文 `:786` 的
      --        `(-ℓ, ℓ_{ι−1})` 型号＋`:388` 的「edge parallel to `ℓ` comes first」要求的
      --        `det (v⃗_{ℓ_{ι−1}}) (v⃗_ℓ) > 0` **符号相反** ⟹ 链上的锥是 `𝓡_{ι−1}` 沿 `ℓ` 的**镜像**。
      --        ⟹ 「`I_paper = ι−1` ↦ `I_lean = 0`」这条映射**唯一的支点**没了，第 198 轮据此定的
      --        洞 3 矛盾**待重判**。详见 `ConeRegion.lean` 头部的 (u3) 判决段。
      --        ⚠ 这**不**说链上的锥造错了，只说那个**认同**为假。
      --        ══ 2026-09-24（第 200 轮，`ConeRegion.lean` 头部「⚖ 裁决（第 200 轮，规矩 17）」节）══
      --        两个候选**均已裁：都死**——(1)「翻 `hnu`」：`det u' vl = -1` 是
      --        `Primitive vl`/`hperp`/`hdetpos`/`hnu` 四条 binder 的算术后果（`RegionNlDict.lean` 的
      --        `nl_eq_neg_dir_vl_and_det_u'`），换坐标换不掉，`no_legal_mirror` 钉死；(2)「链上锥本对应
      --        `:762` 的 Case 2」：Case 2 的真实型号是 `(ℓ,ℓ_J)`（lane-hole3-cone 第 X 轮亲读 `:892`/
      --        `:900`/`:928` 确认，非猜测的 `(-ℓ,ℓ_{ι+m−1})`），符号对得上但 binder 结构（`hbase₁` 是
      --        存在型「成立」陈述）对不上 Case 2 的全称型「处处失败」假设，贴标签救不了。
      --        矛盾的真实位置**改判为**：链上那一档的 `w = extChain d nℓ vl u' i I` 是否等于
      --        `(-1,-1)`（内核见证 `lane-env-refute-mirror.lean` 的 `hstrict_true_iff_dir_eq`：
      --        `hstrict` 在 8 个边界方向里恰在 `w=(-1,-1)` 一档为真，与下标/`u'`/`det u' vl` 符号无关）
      --        ——lane-hole3-cone 独立复核过一遍（2026-09-24），裁决站得住。签名仍不动（规矩 17）。
      --        ⛔ 顺序禁令不变：Claim 4.10 只读不当 binder。
      --
      -- (b) 为什么这条要命 —— `hstrict` 的几何内容（集成者第 197 轮算，逐步）：
      --     `nℓ = -dir vl`、`dir (a,b) = (-b,a)` ⟹ `vl = (v₁,v₂)` 时 `nℓ = (v₂,-v₁)`，于是
      --         `dot nℓ x = v₂x₁ - v₁x₂ = -(v₁x₂ - v₂x₁) = -det vl x`
      --     代进 `hstrict` ⟹ `∀ b ∈ Sφ, dot m a < dot m b → 0 ≤ det vl (b-a)`
      --                   ⟹ 过 `a` 的 `vl`-方向直线在 `dot m > dot m a` 那半边支撑 `Sφ`。
      --     而 `ha_min`＋`ha_end` 把 `a` 钉成 `dot m`-最小边（∥ `w`，因 `hmw`）的 `+w` 起点端，
      --     且 `hwneg : dot nℓ w < 0` ⟹ 同层其余点 `a + t•w`（`t ≥ 1`）的 `dot nℓ` 严格更小。
      --     ⚠⚠ **「起点端」是链侧读数，不是原文侧读数（第 199 轮订正，集成者）。** 链侧无歧义：
      --        `ha_end` 的语句逐字就是「极小层里的点全是 `a + t•w`，`t : ℕ`」（见上方 `:2278` 一带
      --        的批注与 `:2045` 的 `obtain`），`t` 取遍 `ℕ` 而不是 `ℤ` ⟹ `a` 就是 `+w` 方向的**起点**，
      --        这是 binder 自己说的，不依赖任何方位约定。
      --        但**原文侧的同一个端点是起点还是终点，取决于 `w` 与原文定向的对应**，而那一条
      --        **已由第 200 轮裁决改判**（`ConeRegion.lean` 头部「⚖ 裁决（第 200 轮，规矩 17）」节，
      --        lane-hole3-cone 2026-09-24 独立复核过）：原先据以把链侧端点认到原文端点的字典塌了
      --        （lane-towerpkg 报假 (u3)）之后，两个补救候选（翻 `hnu` / 改判为 Case 2）都已证死，
      --        矛盾改判定位到「链上那一档 `w` 是否等于 `(-1,-1)`」，见 `hstrict_true_iff_dir_eq`
      --        （`tmp/wip/lane-env-refute-mirror.lean`）。当前正在查 `hwid` 里的存在量词 `I` 能否钉住
      --        `extChain … I = (-1,-1)`。
      --        ⟹ **本段 (b) 的链侧内容全部有效；凡把 `a` 读成原文某个具名端点的推论一律待裁**
      --        （规矩 17；`hnu` 的符号不动——第 200 轮已确认翻不得）。
      --     ⟹ **`hstrict` ⟺ `a` 是 `𝒮_φ` 的 `dot nℓ`-最大点 ⟺ `ℓ'`-边与 `ℓ`-边环序相邻且
      --         `a` 在二者的公共顶点上。**
      --     ⚠ 「`a` 同时极小化 `dot m` 并极大化 `dot nℓ`」这句**不是第 197 轮的新发现**——上方
      --        `hwrec` 后面那一段（第 167 轮）早就写了。第 197 轮新的只有：该等价是**精确**的
      --        （无额外前提）、它蕴含**边相邻**、以及 (a) 恰好给出那个相邻。
      --     ⚠ `Sφ` 确实是真 `𝒮_φ`：`hSφ : Sφ = d.toDecompData.Sphi`（上方 `obtain`，亲读）
      --        ⟹ `:319` 的 `2m` 条边在链上有对象，上面这套读法不是纸上的。
      --
      -- (c) ⭐ 冲突的锐化形式（不需要任何方位词，集成者第 197 轮）：
      --     `extChain … (len+1) = -vl`（`wtower_last`，`TowerConstruct.lean:398`）。塔已对 `+vl`
      --     封闭，再沿 `-vl` 扫一次 ⟹ 含整条 `vl`-直线 ⟹ 含半平面 ⟹ 不周期（Prop 2.12 / `htop`）。
      --     即 `exists_tower_index` 的「顶上不周期」那条腿是**免费**的 ⟹
      --         `I_lean = len` ⟺ **塔一路周期到顶**。
      --     配 lane-tower-hbase 的内核（`crit_iff_eq_top`：`hstrict` ⟺ 判据 ⟺ `I_lean = len`）
      --     与字典 `I_paper = ι−1−I_lean`（＋ `len = m−2`，未证）⟹
      --         **`hstrict` ⟺ `I_paper = ι−m+1` ＝ `:814` 区间的下端；Claim 4.10 给上端 `ι−1`。**
      --     ⟹ **正面矛盾。**
      --     ⚠⚠ **2026-09-25（第 225 轮，集成者）：本段的 ℕ/ℤ 分叉已裁——答案是 ℤ。**
      --     `I_lean : ℕ`、`len : ℕ`（`CritIffTop.lean:211`/`:221` 的 `{I : ℕ}` 与
      --     `(sortedCand …).length`；`extChain : … → ℕ → ℤ × ℤ`，`TowerConstruct.lean:921`），
      --     但字典 `I_paper = ι−1−I_lean` **必须在 ℤ 里算**：`b3_colle2.txt:814` 逐字
      --     （集成者 2026-09-25 亲读）
      --         "we may consider the smallest integer `ι−m+1 ≤ I ≤ ι−1` such that
      --          `(T^u η)|_{R_I}` is periodic of period `h`"
      --     ——这是一个**货真价实的整数区间**，端点 `ι−m+1` 可以为负（`1 ≤ ι ≤ 2m`，
      --     `Lemma35.lean:112` ⟹ `ι−m+1` 取值 `2−m … m+1`）。ℕ 读法会把 `ι−1−(m−2)` 截断成 `0`
      --     （只要 `ι < m−1`），**是硬错**；凡按 ℕ 写这条字典的地方都要改。
      --     ⚠ 下标名 `ℓ_j` 本身仍按 mod `2m` 解释（`:880`「`ℓ_{ι−1}` antiparallel to `ℓ_{ι+m−1}`」，
      --     `NormalCycle.lean:190`；链侧 `nu` 的 `∀ k, nu (k+m) = -(nu k)`）。
      --     **两件事不矛盾**：区间算术在 ℤ，被索引的直线按 mod `2m` 取。
      --     🔴 **同轮自撤**：本条初稿曾据「`ι−m+1 ≡ ι+m+1 (mod 2m)` 落在 Lemma 3.5(ii) 档」
      --     提出破口 (E)「下标类型译错、矛盾是伪的」。**该说法已作废**——它把 `:814` 的区间误认成
      --     Lemma 3.5 的 `J` 区间（`Lemma35.lean:124`/`:152`）。亲读 `:814` 后确认：`:814` 是
      --     `R_i` 递降链（`:806`「For each integer `ι−m+1 ≤ i ≤ ι−2`」，
      --     `R_{ι−1} ⊂ R_{ι−2} ⊂ ⋯ ⊂ R_{ι−m+1}`）自己的区间，与 Lemma 3.5 的 `J` 无关。
      --     ⟹ `ι−m+1` **确实**是 `:814` 区间的下端，(c) 的矛盾**成立**，破口仍是下面四个。
      --     ⭐ 附带收获（与矛盾同向，非破口）：字典在 `I_lean = len` 处自洽——
      --     `I_paper = ι−1−(m−2) = ι−m+1` ＝ 最小下标 ＝ **最大**区域 `R_{ι−m+1}`（链递降增），
      --     与 (c)「塔一路周期到顶」逐字同义。⟹ (c) 的左半边不必再疑。
      --     破口只有四个，第 197 轮已分派：
      --       (A) 字典方向 `I_paper = ι−1−I_lean` 反了（承重的是 lane-towerpkg 报的未验建模选择
      --           (u3)：`coneRegion B vl u' = 𝓡_{ι−1}`）；
      --       (B) (b) 里「升格成全局 `nℓ`-最大点」那一步不对；
      --       (C) `crit_iff_eq_top` 的 binder 表在 `I = 0` 档不可满足（hbase 自己按 §41 标过非空真性未验）；
      --       (D) `:876` 的 `I` 不是 `:814` 的 `I`。
      --
      -- (d) ⛔ **顺序禁令（不许跳）**：`:860` 明写 `𝒦` 来自 "Due to Claim 4.7 and Lemma 4.1"，
      --     而 Claim 4.10 的证明（`:878`）用 `𝒦` ⟹ **Claim 4.10 在原文里是 Claim 4.7 的下游**，
      --     而本 `hstrict` 坐在 Claim 4.7 的兑现里。⟹ 上面的矛盾**只能当元结论**（「我们译错了一步」），
      --     **绝不许**把 Claim 4.10 当 binder 去证 `hstrict`。即使破口查明是 (A)、判据路线复活，
      --     也要另找「塔一路周期到顶」的独立证明，不得引 Claim 4.10。
      --
      -- (e) 第 196 轮的 (R1)〔内核，hbase 的 `crit_false_below_top` / `crit_iff_eq_top`〕**仍然成立**，
      --     但它单独不再关门——它现在只说「`hstrict` 只在链顶那一档成立」，而那一档对应原文区间的
      --     哪一端，正是 (A) 要判的。(R2)〔原文＋裁决〕同样降级为「依赖 (A)」。
      -- （原 `sorry`，已随 `have` 删除）
    have hroom : ∀ k : ℤ, 0 ≤ k →
        (g + (max τ (t₀ - 1)) • w) - k • w ∈ Rinf →
        Nivat.LE2.dot m ((g + (max τ (t₀ - 1)) • w) - k • w) = lev (N + 1) →
        ∀ b ∈ Sφ, 0 < Nivat.LE2.dot m (b - a) →
          ((g + (max τ (t₀ - 1)) • w) - k • w) + (b - a) ∈ Rinf := by
      intro k _ hP hlevP b hb _
      -- 断行在 `L0` 以下：否则 `cut (N+1) ⊆ Rinf ∩ {dot m ≥ L0} ⊆ tower I` 周期，与 `h2` 矛盾。
      have hlt : lev (N + 1) < L0 := by
        by_contra hge
        exact h2 (hperL0 lev (N + 1) (not_lt.mp hge))
      subst hSφ
      exact hroomBelow a hgenφ.1 ha_min ha_end _ hP (by rw [hlevP]; exact hlt) b hb
    -- ══ 2026-09-24（第 196 轮，集成者）：⭐ 上面这个证明体**扔掉了两条前提** ══
    -- 两个 `_` 分别是 **`0 ≤ k`** 和 **`dot m P = lev (N+1)`**。而
    -- `Hole3Room.room_of_strict`（`Hole3Room.lean:222`）的结论是 `∀ q ∈ Rinf, …`
    -- ——**对 `Rinf` 里任意一点**；它内部归到 `RecessionCone.room_of_cone`，真正的内容是
    -- `b - a ∈ cone(vl, w)`（两条 `det` 不等式）。
    -- ⟹ **现行路线证的东西比要证的强得多**，而强出来的那一截**正好**就是上面 (R1)(R2)(R3)
    --    刚判死的那一整套「`w` 角序极值」的要求（由 (R1) 的机理，判据 ⟺ 锥含住 `Sφ` 上半）。
    --
    -- 而 `P` 根本不是任意点：`P = (g + (max τ (t₀-1)) • w) - k • w`，`0 ≤ k`
    -- ⟹ **`P` 在一条沿 `-w` 的射线上**，对应原文 `:844` 的 `{g + t·v⃗_{ℓ'} : t ≥ t₀}`
    --    （Figure 11(A) 那条；lane-towerpkg 第 195 轮把 `ray g w t₀` 与它对上，三处独立吻合）；
    --    `dot m P = lev (N+1)` 则对应 `:816` 的距离带 `d_n`（`d_0=0<d_1<⋯` 是 `𝓡_I` 内点到
    --    `ℓ'_{𝓡_I}` 距离**取到的全部值**，故相邻层之间无空隙）。
    -- ⟹ ⭐ **洞 3 的下一格 ＝ 让这两条前提承重**：证 `hroom` 时用上「`P` 在射线上」和
    --    「`P` 在最外一层」，绕开 `room_of_cone`。这是目前唯一没被判死的方向。
    -- ⚠ 仍然有效的警告（第 195 轮写的）：在读清 `L1CoverPackage.hcover_of_hedge` /
    --    `step_all_of_hroom` 到底要哪一条之前，不要把「债回到 `hroom`」当成**已定**靶子——
    --    尤其要先确认 `∀ b ∈ Sφ` 这个量词在消费者侧是不是真的全量。
    --
    -- ══ 2026-09-24（第 197 轮，集成者）：上面那条警告**已被 lane-towerpkg 亲读答掉**，
    --    并且「多走的路」到底多在哪里，现在算得出来了 ══
    --
    -- (1) lane-towerpkg 亲读 `HstepAll.lean` 的 `step_all_of_hroom` 与 `L1CoverBridge.lean` 的
    --     `hcover_of_hedge`，三条读数：
    --     * `∀ b ∈ Sφ` **是真全量**（目标的 `∀ b ∈ Sφ.erase a` 逐个透传，`hroom` 只被调用一次），
    --       收窄不到某条边；但有效域本来就只有 `{b : 0 < dot m (b-a)}`（`dot m (b-a) = 0` 那支走
    --       纯 `w`-算术、完全不碰 `hroom`），而 `hstrict` 的定义域与它**逐字相同**
    --       ⟹ 「收窄 `b` ⟹ 判据的 `2m` 条边要求塌一半」这个杠杆**在这一层不存在**。
    --     * `0 ≤ k` 是**白送**的（`k = (min j L : ℤ)`，两个自然数 cast）；
    --       `dot m P = lev (N+1)` **不白送**，由 `P ∈ cut (N+1)` ∧ `P ∉ cut N` 经 `hconsec`
    --       （原文 `:816` 的「`d_n` 枚举所有被取到的距离」）夹成等式。
    --     * 消费者确实把 `∈ Rinf` 加强回 `∈ cut N` 乃至 `∈ overlap`，但用的四条材料
    --       （`hconsec` / `hmvl` / `hc` / `hRinf'`）**全是它自己的形参**，没有一条回头向 `hroom` 要
    --       ⟹ **`∈ Rinf` 不是假象**，`hroom` 的结论强度正好。
    --
    -- (2) ⭐ 于是「多走的路」全部在 **`∀ q ∈ Rinf` 这个量词**上，而不在结论强度上。而且——
    --     **一旦保留 `∀ q`，因式分解是精确的、没有缝**（集成者第 197 轮算）：
    --     由 `nℓ = -dir vl` 得 `dot nℓ x = -det vl x`（推导见上方 `hstrict` 处第 197 轮一节），
    --     再由 `hwneg` 定死 `0 < det vl w`，`room_of_cone` 的两个锥分量化为
    --         第一分量 `0 ≤ det vl w * det (b-a) w` ⟺ `0 ≤ dot m (b-a)`（**就是自己的前件的弱化，含量为零**）
    --         第二分量 `0 ≤ det vl w * det vl (b-a)` ⟺ `dot nℓ (b-a) ≤ 0`（**含量全部在此**）
    --     ⟹ 所谓「锥条件」其实是**半平面条件**，`w` 在里面根本不出现；且它与 `hstrict` 逐字同一条
    --     （lane-tower-hbase 内核：`cone_fst_free` / `cone_snd_iff` / `cone_iff_strict`）。
    --     而消费者有 `htop : ∃ top, ∀ z ∈ Rinf, dot nℓ z ≤ top`（上方 `obtain`，亲读）⟹ 取
    --     `dot nℓ` 在 `Rinf` 上的最大点 `q★`（`ℤ` 值有上界 ⟹ 最大元存在），若 `0 < dot nℓ x` 则
    --     `q★ + x` 越界 ⟹ **`dot nℓ x ≤ 0` 对 `∀ q` 版是必要的**。
    --     ⟹ **`∀ q` 版 `hroom` ⟺ `hstrict`。债 100% 落在 `q`-收窄这一格。**
    --     ⚠ lane-tower-hbase 第 197 轮交过一个「锥条件不必要」的内核反例（右半平面台架），
    --        但那张台架**违反 `htop`**（`nℓ` 由 `hperp`＋`hwneg` 定死为 `(0,-1)`，而 `-z.2` 在右半平面
    --        向下无界）⟹ 它否的是 `room_of_cone` **自己那张 binder 表**下的必要性，**不是链上这张表**。
    --        凡造 `Rinf` 台架，`htop` 必须兑现，否则否不掉任何东西。
    --
    -- (3) ⟹ 收窄到 `P` 之后**唯一可能的新增量**是：`P` 离 `nℓ`-天花板有多远。
    --     `P = g + (K-k)•w`（`K := max τ (t₀-1)`，`0 ≤ k`），`hwneg : dot nℓ w < 0`
    --     ⟹ `P` 比 `g` 低了 `(K-k)·|dot nℓ w|`；`Sφ` 有限 ⟹ `dot nℓ (b-a)` 有上界 `D`。
    --     ⟹ 若 `(K-k)·|dot nℓ w| ≥ D`，`P + (b-a)` 仍在天花板以下。
    --     ⚠ **但「在天花板以下」≠ `∈ Rinf`**（`Rinf` 没证是半平面）。所以真正的下一问是：
    --       **(Q) 从 `hR`(＝`IsLatticeConvexRegion` ＋ `vl`/`w` 两条射线，`Lemma41.lean:688`)、
    --       `htop`、`hwneg`、`hmw`、`hmvl`、`hunb`、`hgap` 这张表，能证出的 `Rinf` 最强下界是什么？**
    --     已知的一条（集成者第 197 轮）：`dot m (z₀ + s•vl + t•w) = dot m z₀ + s·dot m vl ≥ dot m z₀`
    --     （`s,t ≥ 0`，`hmw`，`hmvl`）⟹ `dot m` 在 `cone(vl,w)` 上**有下界**，而 `hunb` 说它在 `Rinf` 上
    --     **无下界** ⟹ **`Rinf` 可证不是 `cone(vl,w)` 的任何平移**，回收锥真包含它。
    --     ⚠ 但这多出来的一截**帮不上 (Q)**：回收锥必落在 `{dot nℓ ≤ 0}` 内（`htop`），而要救的
    --       `b-a` 恰是 `dot nℓ > 0` 的那些。⟹ (Q) 要的是 `Rinf` 在 `P` 附近的**局部厚度**，
    --       不是回收锥。第 197 轮已派 lane-tower-hbase / lane-env-refute。
    --
    -- ══ 2026-09-24（第 197 轮，集成者）：⛔ 上面 (3) 那条「天花板距离」的想法**已被证伪**，撤回 ══
    --
    -- 来源 lane-tower-hlev，集成者重跑 `check1.sh tmp/wip/lane-tower-hlev-levdict.lean`
    -- 复核：`EXIT=0`，12 条声明公理全白（`[propext, (Classical.choice,) Quot.sound]`）。
    --
    -- **证伪的两行理由，恰好就是本声明头自己的两条 binder。**
    --   * `hmw : dot m w = 0` ⟹ `dot m ((g + K•w) - k•w) = dot m g`，**与 `k` 完全无关**
    --     （`HlevLevDict.dot_m_ray_const`）。⟹ 带方程 `dot m P = lev (N+1)` 是**对 `g` 的条件**，
    --     对 `k` 零约束。（上面 `:2214` 那条注释早写过「`dot m` 沿射线恒为 `dot m g`」，
    --     当时当成便利，没注意它同时**掐死了**本格的收窄途径。）
    --   * `hwneg : dot nℓ w < 0` ⟹ `dot nℓ P` 关于 `k` **严格单调且跨度无界**
    --     （`HlevLevDict.dot_nl_ray_strictMono`）。
    --   ⟹ 两个量是**不相交数据的函数**：带方程只看 `g`，天花板距离只看 `k`。
    --     `HlevLevDict.band_carries_no_ceiling_info` 把这件事做成定理：对**任意**预设 `D`，
    --     存在 `0 ≤ k₁ < k₂` 使带方程逐字不变而 `dot nℓ` 之差 `> D`。
    --   ⟹ 按 §54 的判准，「`P` 离天花板的距离」**不是**「带方程 ＋ `0 ≤ k`」的函数，不可推导。
    --
    -- **⚠ 而且方向也反了。** `P ∈ Rinf` ＋ `htop` 给的是 `dot nℓ P ≤ top`，即把 `k` 从**上**卡住；
    -- (3) 要的是 `dot nℓ P ≤ top - D`，是把 `k` 卡得**更紧**。`htop` 出不了这一截，带方程也出不了。
    -- 缺的恰好是天花板下面那 `D` 层，而 `HlevLevDict.exists_gapBand_both_nl` 说明
    -- **最外带上可以坐着 `dot nℓ = top` 的点**。
    --
    -- **⟹ 本格的结论（集成者裁）**：`lev` / `cut` / 射线形这三样对 `nℓ` 方向的信息量**恰好是零**。
    -- 收窄 `q` 的局部厚度**只能从 `hR` 来**（`IsLatticeConvexRegion` ＋ 两条射线，`Lemma41.lean:688`），
    -- 别无来源。(Q) 因此收缩成：**`hR` 单独能不能给出 `P` 附近的厚度**——而 `hR` 的射线是
    -- `vl` / `w` 两条，方向都在 `{dot nℓ ≤ 0}` 里（`hperp` / `hwneg`）。
    --
    -- ⚠ **读法限定（§41/§42）**：hlev 另给了一个台架 `hroom_false_on_outermost_band`
    -- （`Rinf = {z | z.1 ≤ 0}`、`vl=(0,1)`、`nℓ=(1,0)`、`m=(0,1)`、`w=(-1,0)`、`g=(0,-1)`、
    -- `lev n = -n`、`top=0`、`N=K=k=0`、`b-a=(1,1)`），在 `k = 0` 这个最有利的档上 `hroom` 就假。
    -- 但它**未兑现** `hR` / `hunb` / `Sφ = d.Sphi` / `ha_min` / `ha_end` / `hgen`。
    -- ⟹ 它否的是**所列子表**，**不主张 `hroom` 为假**；此处只采纳「(3) 不是收窄途径」这一条。
    --
    -- ══ 2026-09-24（第 197 轮，集成者）：⛔⛔ (Q) 已答，**收窄 `q` 这条路线整条关门** ══
    --
    -- 来源 lane-tower-hlev，集成者重跑 `check1.sh tmp/wip/lane-tower-hlev-thick.lean` 复核：
    -- `EXIT=0`，两条公理全白。
    --   * `HlevThick.no_thickness_from_region`：存在台架同时兑现 `IsRegion Rinf vl w`（**三支逐字**，
    --     含 `IsLatticeConvexRegion` 的 `∃ C, Convex ℝ C ∧ IsClosed C ∧ R = toReal ⁻¹' C`）、
    --     `Prim vl`、`Prim w`、`hw_det`、`hperp`、`hwneg`、`hmw`、`hmvl`、**`htop`**、**`hunb`**，
    --     而仍有 `P ∈ Rinf`、`0 < dot m δ`、`0 < dot nℓ δ`、`P + δ ∉ Rinf`。
    --   * `HlevThick.hroom_false_with_region`：把它与上面那条撤回放到**同一组常数**上一次见证。
    --   台架：`Rinf = {z | z.1 ≤ 0}`、`C = {x : ℝ×ℝ | x.1 ≤ 0}`、`vl=(0,1)`、`w=(-1,0)`、
    --   `nℓ=(1,0)`、`m=(0,1)`、`top=0`；另 `g=(0,-1)`、`lev n = -n`、`N=0`、`K=k=0`、`b-a=(1,1)`。
    --
    -- **机制一句话**：`IsRegion` 要的两条射线方向 `vl`、`w` 都躺在 `{dot nℓ ≤ 0}` 里
    -- （`hperp` 给 `=0`、`hwneg` 给 `<0`），而 `IsLatticeConvexRegion` 只要求「某个闭凸集的整点原像」
    -- ⟹ **左闭半平面逐字满足，它朝 `dot nℓ > 0` 的厚度恰好是零**。
    -- `htop` 非但不帮忙，它正是把区域压在天花板下的那条；`hunb` 由 `dot m` 方向独立满足，与 `nℓ` 无关。
    --
    -- **⟹ 穷举结论（集成者裁，本轮亲自补完最后一条）**：约束 `Rinf` 的 binder 只有
    -- `hR` / `htop` / `hunb` / `h0` / `hgap` / `hconsec` / `hRinf'` 七条。
    -- 其中 `hgap`/`hconsec` 经上面那条撤回为零，`hR`/`htop`/`hunb` 经本条为零，
    -- 而 **`hRinf' : ∀ z ∈ Rinf, z + c • vl ∈ Rinf`（`:2090`）同样为零**——
    -- 两个理由：① `hperp : dot nℓ vl = 0` ⟹ 沿 `vl` 平移不改变 `dot nℓ`，出不了 `nℓ` 方向的厚度；
    -- ② 上述台架**本身就满足它**（`Rinf = {z | z.1 ≤ 0}`、`vl = (0,1)` ⟹ 第一分量不动）。
    -- 〔hlev 把这条标为「待补一条」，集成者本轮补完，故穷举成立。〕
    -- 剩下的 `ha_min` / `ha_end` / `hgen` / `Sφ = d.Sphi` 全是关于 `Sφ` 与 `a` 的，
    -- **一个字都不约束 `Rinf`**，而 `hroom` 的结论是 `… ∈ Rinf`。
    --
    -- **⟹ 本格的最终裁决：`hroom` 不存在「比 `hstrict` 弱」的走法。**
    -- 配上面那条「`∀ q` 版 ＋ `htop` ⟺ `hstrict`」的充要性 ⟹ 洞 3 的唯一出路回到 `hstrict` 本身，
    -- 即破口 (A)(B)(C)(D)（见 `hstrict` 那一格的第 197 轮批注）。
    -- ⚠ 读法限定（§41/§42）：以上台架**未兑现** `hξ` / `hgen` / `Sφ = d.Sphi` / `ha_min` / `ha_end`
    -- / `hc` / `τ` / `ε` 那一族 ⟹ 否的是所列子表，**不主张 `hroom` 为假**；
    -- 主张的是「从约束 `Rinf` 的那七条 binder 推不出任何朝 `dot nℓ > 0` 的厚度」。
    exact Nivat.L1CoverPackage.hcover_of_hedge hR hm0 hmw hmvl hc
      (Nivat.LE2.prim_iff_primitive.mpr hw_prim) hwneg htop hconsec
      hlev_mono hRinf' (hedge N h1 h2) g hgS hgD t₀ ht₀
      (Nivat.L1CoverPackage.step_all_of_hroom hmw hmvl hc hconsec hRinf' ha_min ha_end g τ t₀ hroom)
  exact exists_cutResidualR_of_claim46_ofPieces hξ d hgen henv hBfin hBne
    hunimod hvl_prim hc hperp hnu hbase₁ v τ ε Rinf w hw_det hw_prim m hmw hmvl Sφ a hgenφ hR
    lev b₀ hlev0 hlev hexh hgap (hbase lev hlev0) hinf hline hcover

/-- **阶段二入口**（两阶段拆分第二步，2026-09-20）。

原文：b3_colle2.txt:806-856。第二阶段的**所有数据都换了一套坐标框**：

* 基集不再是有限的 `B`，而是区域 `𝓡_I`（`:806-812`：`𝓡_{ι−1} ⊂ ⋯ ⊂ 𝓡_{ι−m+1}`，
  `I` 取**最小**的使 `(T^u η)|𝓡_I` 仍以 `h` 为周期的指标）；
* 推进方向不再是 `v⃗_{ℓ_{ι−1}}`，而是 `v⃗_{ℓ_{I−1}}`（`:812` 的 `𝓡^n_I` 定义）；
* 角点 `a`（Figure 11(B)，`:848-856`）挂在**这个**方向上。

**本条只做装配，不做数学**：把「某个框里的 `hbase` ＋ 同框的角点」接成 `WedgeResidualR`。
它与阶段一的唯一区别是 **`u₂` 上没有 `hadj`**——`CornerAdjClash` 的冲突因此不适用。
`ha` / `hcorner` 本身在任何方向上都是免费的（`WedgeAssemble.exists_shear_corner_data`），
真债是「`hbase` 落在角点所在的那个框里」，即 `:806-856` 的 `𝓡^N_I` 极大性论证。 -/
theorem wedgeResidualR_of_stage2_frame
    {e : ℤ × ℤ} (hξ : IsMinimalCounterexample ξ) (d : DecompDataZ ξ)
    (hS : S.Nonempty) {c : ℤ} (hc : 0 < c) (hvl_prim : Primitive vl)
    {R : Set (ℤ × ℤ)} {u₂ b₀ : ℤ × ℤ} {k : ℕ}
    (hunimod₂ : det u₂ vl = 1 ∨ det u₂ vl = -1) (hb₀ : b₀ ∈ R)
    (hbase₂ : Nivat.Colle41.PeriodOn (T e ξ)
      (Nivat.ColleReg.chainFull R vl u₂ b₀ k) (c • vl))
    {a : ℤ × ℤ} (ha : a ∈ d.toDecompData.Sphi)
    (hcorner : ∀ b ∈ d.toDecompData.Sphi,
      0 ≤ Nivat.LE2.dot (expNormal u₂ vl) (b - a) ∧
        0 ≤ Nivat.L1Line0.uCoord u₂ vl a b) :
    Nonempty (L1Claim.WedgeResidualR ξ S vl) := by
  have h0 : u₂ - (0 : ℤ) • vl = u₂ := by simp
  exact Nivat.WedgeAssemble.nonempty_wedgeResidualR_of_hbase_at_shear hξ d hb₀ hunimod₂ hc
    hvl_prim 0 k (by rw [h0]; exact hbase₂) ha (by rw [h0]; exact hcorner) hS

/-- **同一条结论，`hchain` 与剪切处的 `hstep` 已就地打掉**（接链第二轮，2026-09-20）。

与 `wedgeResidualR_of_cone_hmono_at_shear` 结论**逐字相同**，差别只在前提：

* **`hchain` 没了。** 上一版把 `chainFull ⊆ coneRegion` 当前提，而
  `Nivat.ConeHbase.not_chainFull_subset_coneRegion` 是该包含在一般情形为假的内核见证——
  那条前提**不可兑现**。本版改走 `StrictWindow.hbase_of_cone_halfStrip_of_hmono_of_argmax`
  （`StrictWindow.lean:1170`），它用 `LE2.chainFull_subset_coneRegion_of_argmax_general`
  （`LineIndex.lean:409`）把包含**证出来**，代价是落在**平移底** `shift (-(k•vl)) B` 上，
  所以下面四条几何前提 `hD`/`hcone`/`hstrip`/`hmono` 都在平移底上陈述。
  `k = 0` 时平移是恒等。结论里的 `chainFull B vl (u' - K • vl) b₀ k` 仍在原 `B` 上。
* **剪切处的 `hstep` 没了。** 只要未剪切的 `hnu : ⟪nℓ, u'⟫ = -1` 与 `hperp : ⟪nℓ, vl⟫ = 0`，
  `⟪nℓ, u' - K • vl⟫ = -1` 对**任何** `K` 成立，本证明就地算出来。
* **`hb₀` 没了。** `b₀` 由 `StrictWindow.exists_argmax_base`（`:1212`）从 `B.Finite` +
  `B.Nonempty` 选出，同时兑现 `WedgeAssemble` 那侧要的 `b₀ ∈ B` 与 §12 要的 `hb₀max`。

**剩下的唯一几何债是 `hmono`**（`hD`/`hcone`/`hstrict`/`hcorner` 各有在建生产者）。
`EnvFit.exists_shear_hmono_of_edges`（`EnvFit.lean:1109`）已把它**证出来**：在
`IsLatticeConvexRegion B` ＋ `-nℓ ∈ E B` ＋ `nℓ ∈ E B` 下存在剪切使 `hmono` 成立
（原文 `b3_colle2.txt:774`「`𝒮` 有平行于 `ℓ` 和平行于 `-ℓ` 的边」，`:777` 的 enveloped 把两条边
从 `𝒮_φ` 搬到 `B`）。本定理**没有**就地调用它，原因写在下面，是一条真问题不是接线疏漏。

**🔴 两个 `K` 的方向相反，且已判定为不可调和（2026-09-20，有内核见证）**：
`EnvFit.exists_shear_hmono_of_edges` 自己选的是 `K = -(ψmax − ψmin) ≤ 0`（`EnvFit.lean:1126`），
而 `L1StraddleWedge.exists_corner_shear`（`L1StraddleWedge.lean:424`）选的是
`K = max M 0 ≥ 0`（`:436`）。`hmono` 与 `hcorner` 在本定理里**必须是同一个 `K`**。
见证：`EnvFit.no_nonneg_shear_hmono`（`EnvFit.lean:1452`，底集 `Bslant`（`:1369`）有限、非空、
`PosArea`、格凸、两条边俱全）证明**任何 `K ≥ 0` 都不给 `hmono`**。所以不是「先各自推广再合成」，
两边根本没有公共的 `K`。

**诊断：剪切是我们的发明，`K = 0` 才是原文。** 上面第 2850 行那句
「`:777` 的 enveloped 把两条边从 `𝒮_φ` 搬到 `B`」只用了 Def 3.2 的**一半**。
另一半是 `b3_colle2.txt:402` 的 `|E(𝒯)| = |E(𝒰)|`，经 `Nivat.LE2.Enveloped.E_eq`
（`LatticeEdges.lean:1657`）给出 `E B = E 𝒮_φ`——`B` 带的是 `𝒮_φ` 的**全部 `2m` 条**边法向，
不止那两条。而 `b3_colle2.txt:764`（`:424`、`:541` 同文）写死了指标的含义：
「`ℓ₁,…,ℓ_{2m}` 是平行于 `𝒮_φ` **各边**的有向直线的一个枚举，平行于 `ℓ_{i+1}` 的边是平行于
`ℓ_i` 的边的**后继**，指标模 `2m`」。故 `:780` 的扫掠方向 `u' = v_{ℓ_{ι-1}}` 是 `ℓ_ι = ℓ`
的**循环前驱**，**本身就是 `B` 的一条边方向**。`Bslant` 只有 4 条边法向、不含 `-expNormal u' vl`，
所以它证伪的是**删掉 enveloped 之后**的弱化版（硬规矩 10 的「比原文弱 = 白烧算力」一侧，
责任在派工，不在 lane）。剪切到 `K = -1` 让 `u'' = (1,1)` 变成 `Bslant` 的边方向——
**剪切干的正是 enveloped 白给的那件事**。

在建替代：`EnvFit.hmono_of_lean`（`K = 0`，前提
`hlean : ∃ b* ∈ B, dot nℓ b* = cz ∧ ∀ b ∈ B, ψ b* ≤ ψ b`，即 `B` 的 `ψ`-最左点落在
`u'` 远端那层）＋ `L1StraddleWedge.exists_corner_of_adjacent`（`K = 0`，前提为后继关系）。
本定理与 `K` 显式参数**暂留**（`PROTOCOL.md` §14）：它是「两条各自公理干净的引理仍可能无法合成」
的实例，删掉就丢了这条教训。

原文：b3_colle2.txt:792-804（Figure 10 的放置归纳）、`:780`（区域与扫掠方向的定义）、
`:774`（两条边）、`:777`（enveloped）、`:402`（Def 3.2）、`:764`（后继枚举）。 -/
theorem wedgeResidualR_of_cone_hmono_at_shear_of_argmax
    {e : ℤ × ℤ} (hξ : IsMinimalCounterexample ξ) (d : DecompDataZ ξ)
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S) (hS : S.Nonempty)
    {Sw : Finset (ℤ × ℤ)} {a₀ : ℤ × ℤ}
    {B : Set (ℤ × ℤ)} {u' nℓ : ℤ × ℤ} {c cz : ℤ}
    -- 🔴 2026-09-21 集成者：`GeneratesAt ξ Sw a₀` 换成原文 `:786`+`:790`+`:792` 的捆绑形状。
    -- 原文从未断言 `𝒮_{φ_ι}` 生成 `ξ` 本身，只断言它在 `ZMod p` 里生成差 `η − η̄_{ι₀}`。
    (hSwgen : Nivat.SweepLines.ReducedGeneratesAt ξ Sw a₀ (c • vl))
    (ha₀ : a₀ ∈ Sw) (hconv : Nivat.LatticeConvex (Sw.erase a₀))
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hc : 0 < c) (hvl_prim : Primitive vl) (K : ℤ) (k : ℕ)
    (hD : ∀ z ∈ Nivat.LE2.halfStrip (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl,
      (T e ξ) z = T (c • vl) (T e ξ) z)
    (hperp : Nivat.LE2.dot nℓ vl = 0)
    (hnu : Nivat.LE2.dot nℓ u' = -1)
    (hstrict : ∀ z ∈ Sw.erase a₀, Nivat.LE2.dot nℓ a₀ < Nivat.LE2.dot nℓ z)
    (hcone : ∀ w ∈ Nivat.ConeRegion.coneRegion (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl
        (u' - K • vl),
      Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ Sw.erase a₀, Nivat.LE2.dot nℓ (z + (w - a₀)) < cz →
        z + (w - a₀) ∈ Nivat.ConeRegion.coneRegion (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl
          (u' - K • vl))
    (hstrip : ∀ w ∈ Nivat.ConeRegion.coneRegion (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl
        (u' - K • vl),
      Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ Sw.erase a₀, cz ≤ Nivat.LE2.dot nℓ (z + (w - a₀)) →
        z + (w - a₀) ∈ Nivat.LE2.halfStrip (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl)
    (hmono : ∀ b ∈ Nivat.LE2.shift (-((k : ℤ) • vl)) B, ∀ t : ℕ,
      cz ≤ Nivat.LE2.dot nℓ b - (t : ℤ) →
        b + (t : ℤ) • (u' - K • vl) ∈
          Nivat.LE2.halfStrip (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl)
    {a : ℤ × ℤ} (ha : a ∈ d.toDecompData.Sphi)
    (hcorner : ∀ b ∈ d.toDecompData.Sphi,
      0 ≤ Nivat.LE2.dot (expNormal (u' - K • vl) vl) (b - a) ∧
        0 ≤ Nivat.L1Line0.uCoord (u' - K • vl) vl a b) :
    Nonempty (L1Claim.WedgeResidualR ξ S vl) := by
  -- **本体现在逐字等于「阶段一 ＋ 阶段二」**（两阶段拆分，2026-09-20）：上面两条各自独立，
  -- 这里只是把它们接起来，所以拆分是**忠实的**（不是新陈述，公理输出不变）。
  obtain ⟨b₀, hb₀, hbase⟩ :=
    exists_hbase_of_cone_hmono_at_shear_of_argmax hSwgen ha₀ hconv hBfin hBne hunimod K k
      hD hperp hnu hstrict hcone hstrip hmono
  have hunimod' : det (u' - K • vl) vl = 1 ∨ det (u' - K • vl) vl = -1 := by
    rwa [Nivat.L1StraddleWedge.det_shear]
  exact wedgeResidualR_of_stage2_frame hξ d hS hc hvl_prim hunimod' hb₀ hbase ha hcorner

/-! ### 平移底与原底之间的两条字典

`wedgeResidualR_of_cone_hmono_at_shear_of_argmax` 的四条几何前提落在平移底
`shift (-(k•vl)) B` 上（`StrictWindow.hbase_of_cone_halfStrip_of_hmono_of_argmax` 的形状），
而 `EnvFit` 那侧的生产者全部在原底 `B` 上陈述。搬运所需的事实**大部分已经存在**
（`PROTOCOL.md` §20）：`Nivat.LE2.E_shift`（`LatticeEdges.lean`，`@[simp]`）、
`Nivat.LE2.isLatticeConvexRegion_shift`、`Nivat.LE2.shift_eq_image`（同文件，
有限性与非空性由它一行转出）。⚠ 第 201 轮删号留名：原记 `E_shift` 在 `:615`，实测声明头
在 `:689`，同块另两条同批漂移，一并去号；按名字 `grep`。**真正缺的只有下面两条**，且只有本文件一个消费者，
所以就地落在这里而不是新开模块。

⚠ 另一半在 Wbox 的实测里：因为 `dot nℓ vl = 0`，沿 `vl` 的平移**不改变任何 `nℓ` 层号**
（`dot nℓ (z - c) = dot nℓ z`），所以 `cz` 与 `hczB` 在两个底之间**不需要调整**。 -/

/-- **`halfStrip` 与 `shift` 交换。** `halfStrip (shift c B) vl = shift c (halfStrip B vl)`。 -/
theorem halfStrip_shift (c : ℤ × ℤ) (B : Set (ℤ × ℤ)) (w : ℤ × ℤ) :
    Nivat.LE2.halfStrip (Nivat.LE2.shift c B) w
      = Nivat.LE2.shift c (Nivat.LE2.halfStrip B w) := by
  ext z
  constructor
  · rintro ⟨b, hb, t, rfl⟩
    refine ⟨b - c, hb, t, ?_⟩
    abel
  · rintro ⟨b, hb, t, ht⟩
    refine ⟨b + c, ?_, t, ?_⟩
    · show b + c - c ∈ B
      simpa using hb
    · have : z - c = b + (t : ℤ) • w := ht
      have hz : z = b + (t : ℤ) • w + c := by
        rw [← this]; abel
      rw [hz]; abel

/-- **`coneRegion` 与 `shift` 交换。** -/
theorem coneRegion_shift (c : ℤ × ℤ) (B : Set (ℤ × ℤ)) (w u : ℤ × ℤ) :
    Nivat.ConeRegion.coneRegion (Nivat.LE2.shift c B) w u
      = Nivat.LE2.shift c (Nivat.ConeRegion.coneRegion B w u) := by
  ext z
  rw [Nivat.ConeRegion.mem_coneRegion_iff]
  show _ ↔ z - c ∈ Nivat.ConeRegion.coneRegion B w u
  rw [Nivat.ConeRegion.mem_coneRegion_iff]
  constructor
  · rintro ⟨b, hb, s, t, rfl⟩
    refine ⟨b - c, hb, s, t, ?_⟩
    abel
  · rintro ⟨b, hb, s, t, ht⟩
    refine ⟨b + c, ?_, s, t, ?_⟩
    · show b + c - c ∈ B
      simpa using hb
    · have hz : z = b + (s : ℤ) • w + (t : ℤ) • u + c := by
        rw [← ht]; abel
      rw [hz]; abel

/-- **`hmono` 沿任何 `nℓ`-零平移不变。**  `wedgeResidualR_of_cone_hmono_at_shear_of_argmax`
的 `hmono` 落在平移底 `shift (-(k•vl)) B` 上，而 `EnvFit` 那侧的生产者全在原底 `B` 上陈述；
因为 `dot nℓ vl = 0`，平移向量 `c = -(k•vl)` 满足 `dot nℓ c = 0`，层号不动，
所以搬运只用到 `halfStrip_shift`。 -/
theorem hmono_shift {B : Set (ℤ × ℤ)} {nℓ u' w c : ℤ × ℤ} {cz : ℤ}
    (hc : Nivat.LE2.dot nℓ c = 0)
    (hmono : ∀ b ∈ B, ∀ t : ℕ, cz ≤ Nivat.LE2.dot nℓ b - (t : ℤ) →
      b + (t : ℤ) • u' ∈ Nivat.LE2.halfStrip B w) :
    ∀ b ∈ Nivat.LE2.shift c B, ∀ t : ℕ, cz ≤ Nivat.LE2.dot nℓ b - (t : ℤ) →
      b + (t : ℤ) • u' ∈ Nivat.LE2.halfStrip (Nivat.LE2.shift c B) w := by
  intro b hb t hlev
  have hbB : b - c ∈ B := hb
  have hdot : Nivat.LE2.dot nℓ (b - c) = Nivat.LE2.dot nℓ b := by
    rw [Nivat.LE2.dot_sub, hc, sub_zero]
  have hmem := hmono (b - c) hbB t (by rw [hdot]; exact hlev)
  rw [halfStrip_shift]
  show b + (t : ℤ) • u' - c ∈ Nivat.LE2.halfStrip B w
  have he : b + (t : ℤ) • u' - c = (b - c) + (t : ℤ) • u' := by abel
  rw [he]
  exact hmem

/-- **同一条结论，`hmono` 已就地打掉，`K = 0`**（接链第三轮，2026-09-20）。

与 `wedgeResidualR_of_cone_hmono_at_shear_of_argmax` 结论**逐字相同**，差别有两处：

* **`hmono` 没了**，由 `Nivat.EnvFit.hmono_of_lean_of_enveloped`（`EnvFit.lean:1981`）就地产出，
  再经 `hmono_shift` 搬到平移底。代价是三条新前提 `henv` / `hEbot` / `hEtop` / `hlean`，
  它们全部有原文对应物：`henv` 是 `b3_colle2.txt:777` 的 enveloped（Definition 3.2 在 `:402`），
  `hEbot`/`hEtop` 是 `:774`「`𝒮` 有平行于 `ℓ` 与 `-ℓ` 的边」，`hlean` 是
  `𝒮` 的 `ψ`-最小点落在 `nℓ` 层 `cz` 上。
* **`K` 参数没了，固定为 `0`。** 诊断见上一条定理的 docstring：剪切是我们的发明，
  `b3_colle2.txt:764` 的后继枚举已经让 `u' = v_{ℓ_{ι-1}}` 本身是 `B` 的一条边方向，
  不需要把它剪出来。`hcorner` 因此也在未剪切的 `u'` 上，与
  `L1StraddleWedge` 那侧的 `K = 0` 出口对齐。

**`hlean` 已不再是前提**（2026-09-20 二次接链）。`Nivat.EnvFit.hmono_of_adjacent_of_enveloped`
（`EnvFit.lean:2404`）把它**产出**而不是假设：代价是 `hcz` / `hczmem`（`cz` 是 `B` 的 `nℓ`-最低层，
对有限非空 `B` 恒可取）与 `hadj`。`hadj` 是 `b3_colle2.txt:764` 的相邻性——
「`ℓ_{ι-1}` 是 `ℓ_ι` 在边方向循环序里的前驱」——写成一条 `dot` 符号条件：
没有边法向严格落在 `-nℓ`（`ℓ`-边）与 `-μ`（`u'`-边）之间的那个锥里。循环序本身不需要形式化。

原文：b3_colle2.txt:792-804、`:780`、`:777`、`:774`、`:764`、`:402`。 -/
theorem wedgeResidualR_of_cone_of_enveloped
    {e : ℤ × ℤ} (hξ : IsMinimalCounterexample ξ) (d : DecompDataZ ξ)
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S) (hS : S.Nonempty)
    {Sw : Finset (ℤ × ℤ)} {a₀ : ℤ × ℤ}
    {B Senv : Set (ℤ × ℤ)} {u' nℓ : ℤ × ℤ} {c cz : ℤ}
    -- 🔴 2026-09-21 集成者：`GeneratesAt ξ Sw a₀` 换成原文 `:786`+`:790`+`:792` 的捆绑形状。
    -- 原文从未断言 `𝒮_{φ_ι}` 生成 `ξ` 本身，只断言它在 `ZMod p` 里生成差 `η − η̄_{ι₀}`。
    (hSwgen : Nivat.SweepLines.ReducedGeneratesAt ξ Sw a₀ (c • vl))
    (ha₀ : a₀ ∈ Sw) (hconv : Nivat.LatticeConvex (Sw.erase a₀))
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hc : 0 < c) (hvl_prim : Primitive vl) (k : ℕ)
    (hD : ∀ z ∈ Nivat.LE2.halfStrip (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl,
      (T e ξ) z = T (c • vl) (T e ξ) z)
    (hperp : Nivat.LE2.dot nℓ vl = 0)
    (hnu : Nivat.LE2.dot nℓ u' = -1)
    (hstrict : ∀ z ∈ Sw.erase a₀, Nivat.LE2.dot nℓ a₀ < Nivat.LE2.dot nℓ z)
    (hESfin : (Nivat.LE2.E Senv).Finite)
    (henv : Nivat.LE2.Enveloped Senv B)
    (hEbot : -nℓ ∈ Nivat.LE2.E Senv) (hEtop : nℓ ∈ Nivat.LE2.E Senv)
    (hcz : ∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b)
    (hczmem : ∃ b ∈ B, Nivat.LE2.dot nℓ b = cz)
    (hadj : ∀ n ∈ Nivat.LE2.E Senv,
      ¬ (Nivat.LE2.dot n vl < 0 ∧ 0 < Nivat.LE2.dot n u'))
    (hcone : ∀ w ∈ Nivat.ConeRegion.coneRegion (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl u',
      Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ Sw.erase a₀, Nivat.LE2.dot nℓ (z + (w - a₀)) < cz →
        z + (w - a₀) ∈
          Nivat.ConeRegion.coneRegion (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl u')
    (hstrip : ∀ w ∈ Nivat.ConeRegion.coneRegion (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl u',
      Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ Sw.erase a₀, cz ≤ Nivat.LE2.dot nℓ (z + (w - a₀)) →
        z + (w - a₀) ∈ Nivat.LE2.halfStrip (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl)
    {a : ℤ × ℤ} (ha : a ∈ d.toDecompData.Sphi)
    (hcorner : ∀ b ∈ d.toDecompData.Sphi,
      0 ≤ Nivat.LE2.dot (expNormal u' vl) (b - a) ∧
        0 ≤ Nivat.L1Line0.uCoord u' vl a b) :
    Nonempty (L1Claim.WedgeResidualR ξ S vl) := by
  have h0 : u' - (0 : ℤ) • vl = u' := by simp
  have hmonoB := Nivat.EnvFit.hmono_of_adjacent_of_enveloped hunimod hESfin henv hBfin hBne
    hperp hnu hEbot hEtop hcz hczmem hadj
  have hshift0 : Nivat.LE2.dot nℓ (-((k : ℤ) • vl)) = 0 := by
    have hexp : Nivat.LE2.dot nℓ (-((k : ℤ) • vl))
        = -((k : ℤ) * Nivat.LE2.dot nℓ vl) := by
      simp only [Nivat.LE2.dot, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul]
      ring
    rw [hexp, hperp]; ring
  have hmonoS := hmono_shift (w := vl) hshift0 hmonoB
  exact wedgeResidualR_of_cone_hmono_at_shear_of_argmax hξ d hSgen hS hSwgen ha₀ hconv hBfin hBne
    hunimod hc hvl_prim 0 k hD hperp hnu hstrict (by rw [h0]; exact hcone)
    (by rw [h0]; exact hstrip) (by rw [h0]; exact hmonoS) ha (by rw [h0]; exact hcorner)

/-- **Case 1 形态：`henv` / `hESfin` / `hEbot` / `hEtop` 四条全部就地打掉**（接链第三轮，2026-09-20）。

与上一条结论逐字相同。差别在于**包络与两条边不再是前提**：

* **`henv` 直接来自 `hcase1`。** `Case1 ξ xper d.Sphi vl`（`CaseSplit.lean:82`）按定义就是
  `∃ B, EnvOf (↑d.Sphi) B ∧ ∃ u, …`，所以本定理只要 `henv : EnvOf (↑d.Sphi) B`——
  它是 `hcase1` 解构的第一个分量，在 `exists_wedgeResidualR`（`:1210` 的洞）的 binder 下**白给**。
* **`hESfin` 免费**：`d.Sphi` 是 `Finset`，`Nivat.LE2.finite_E_of_finite`（`LatticeEdges.lean:317`）
  不要 `PosArea`。
* **`hEbot` / `hEtop` 归约到一条正交性**：`DecompData.mem_E_Sphi_of_dot_eq_zero`
  （`FaceDistinct.lean:146`）与 `DecompData.neg_mem_E_Sphi_of_dot_eq_zero`（`:159`）说
  「与某条分解周期 `d.h i` 正交的本原法向是 `d.Sphi` 的边法向」，两条都不要极小性。
  于是 `b3_colle2.txt:774`「`𝒮` 有平行于 `ℓ` 与 `-ℓ` 的边」在链上的兑现物就是
  `hprim : Prim nℓ` ＋ `∃ i, ⟪nℓ, d.h i⟫ = 0`，即**`vl` 平行于某条分解周期**——
  这正是 `:774` 说的那件事，不是加强。

**剩下的前提里只有 `hlean` 没有生产者**（其余 `hD`/`hcone`/`hstrip`/`hstrict`/`hcorner`
各有在建 lane）。`hlean` 的预期出口见 `EnvFit.hmono_of_lean_of_enveloped` 的 docstring。

原文：b3_colle2.txt:758（Case 1）、`:777`（enveloped）、`:774`（两条边）、`:402`（Def 3.2）。 -/
theorem wedgeResidualR_of_case1_of_cone
    {e : ℤ × ℤ} (hξ : IsMinimalCounterexample ξ) (d : DecompDataZ ξ)
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S) (hS : S.Nonempty)
    {Sw : Finset (ℤ × ℤ)} {a₀ : ℤ × ℤ}
    {B : Set (ℤ × ℤ)} {u' nℓ : ℤ × ℤ} {c cz : ℤ}
    -- 🔴 2026-09-21 集成者：`GeneratesAt ξ Sw a₀` 换成原文 `:786`+`:790`+`:792` 的捆绑形状。
    -- 原文从未断言 `𝒮_{φ_ι}` 生成 `ξ` 本身，只断言它在 `ZMod p` 里生成差 `η − η̄_{ι₀}`。
    (hSwgen : Nivat.SweepLines.ReducedGeneratesAt ξ Sw a₀ (c • vl))
    (ha₀ : a₀ ∈ Sw) (hconv : Nivat.LatticeConvex (Sw.erase a₀))
    (henv : Nivat.LE2.EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) B)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hc : 0 < c) (hvl_prim : Primitive vl) (k : ℕ)
    (hD : ∀ z ∈ Nivat.LE2.halfStrip (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl,
      (T e ξ) z = T (c • vl) (T e ξ) z)
    (hperp : Nivat.LE2.dot nℓ vl = 0)
    (hnu : Nivat.LE2.dot nℓ u' = -1)
    (hstrict : ∀ z ∈ Sw.erase a₀, Nivat.LE2.dot nℓ a₀ < Nivat.LE2.dot nℓ z)
    (hprim : Nivat.LE2.Prim nℓ) (i : Fin d.toDecompData.m)
    (hdoth : Nivat.LE2.dot nℓ (d.toDecompData.h i) = 0)
    (hcz : ∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b)
    (hczmem : ∃ b ∈ B, Nivat.LE2.dot nℓ b = cz)
    (hadj : ∀ n ∈ Nivat.LE2.E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)),
      ¬ (Nivat.LE2.dot n vl < 0 ∧ 0 < Nivat.LE2.dot n u'))
    (hcone : ∀ w ∈ Nivat.ConeRegion.coneRegion (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl u',
      Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ Sw.erase a₀, Nivat.LE2.dot nℓ (z + (w - a₀)) < cz →
        z + (w - a₀) ∈
          Nivat.ConeRegion.coneRegion (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl u')
    (hstrip : ∀ w ∈ Nivat.ConeRegion.coneRegion (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl u',
      Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ Sw.erase a₀, cz ≤ Nivat.LE2.dot nℓ (z + (w - a₀)) →
        z + (w - a₀) ∈ Nivat.LE2.halfStrip (Nivat.LE2.shift (-((k : ℤ) • vl)) B) vl)
    {a : ℤ × ℤ} (ha : a ∈ d.toDecompData.Sphi)
    (hcorner : ∀ b ∈ d.toDecompData.Sphi,
      0 ≤ Nivat.LE2.dot (expNormal u' vl) (b - a) ∧
        0 ≤ Nivat.L1Line0.uCoord u' vl a b) :
    Nonempty (L1Claim.WedgeResidualR ξ S vl) :=
  wedgeResidualR_of_cone_of_enveloped hξ d hSgen hS hSwgen ha₀ hconv hBfin hBne hunimod hc hvl_prim k
    hD hperp hnu hstrict
    (Nivat.LE2.finite_E_of_finite (d.toDecompData.Sphi.finite_toSet))
    (Nivat.LE2.envOf_iff.mp henv)
    (d.toDecompData.neg_mem_E_Sphi_of_dot_eq_zero hprim i hdoth)
    (d.toDecompData.mem_E_Sphi_of_dot_eq_zero hprim i hdoth)
    hcz hczmem hadj hcone hstrip ha hcorner

/-- **`k = 0` 特例：四条几何义务改写在未平移的 `B` 上**（接链第四轮，2026-09-20）。

`k` 是平移指标，`Nivat.LE2.shift (-((k:ℤ)•vl)) B` 在 `k = 0` 时就是 `B`
（`shift 0 B = {z | z - 0 ∈ B} = B`）。`k` 从 `chainFull` 那条老路继承下来，
**消费者可以自由取值**，所以取 `0`：`hD` / `hcone` / `hstrip` 三条立刻变成关于 `B` 自身的陈述。

这条的用处是**派工面**：`hcone`（`SweepLines`）、`hstrip`（`SweepBase`）、`hD`（`StrictWindow`）
三条义务原先都要带着 `shift (-((k:ℤ)•vl))` 写，平移层和几何内容纠缠在一起；现在它们各自
就是原文 `:784`（`𝓡_{ι-1}`）、`:794`（`H_B(ℓ) ∪ A₁`）、`:778`（`(T^u η)|H_B(ℓ) = x_per|H_B(ℓ)`）
的直译。若将来需要非零 `k`，用上面那条带 `k` 的版本，本条不阻挡。

原文：b3_colle2.txt:758、`:778`、`:784`、`:794`。

🟢 **2026-09-20 17:xx 裁决并落地：`OPEN.md #15` = (B)，停线解除。** 下面那条 2026-09-20
早些时候的停线警告**内容全对，处置已完成**，逐字保留（`PROTOCOL.md` §14）。

**做了什么**：这一族五条装配器（`:1150` / `:1230` / `:1372` / `:1441` / `:1523` / `:1660`）
的签名统一加了一对新 binder `{Sw : Finset (ℤ × ℤ)}` + `hSwgen : IsGeneratingSet ξ Sw`，
并把 `ha₀` / `hconv` / `hstrict` / `hcone` / `hstrip` 五条**全部从 `S` 挂到 `Sw` 上**；
`hSgen` / `hS` 留在 `S` 上不动。`check1.sh` EXIT=0。

**为什么可以这样拆**（复核过，不是读法）：`S` 在 `WedgeResidualR`（`L1Claim.lean:928`）里
只出现在 `hline` / `hstraddle` 的 `derivedQ ε u' (S.image (· + v))`，**`hbase` 字段一个 `S` 都没有**；
而 `hstrict` / `hcone` / `hstrip` / `ha₀` / `hconv` 这五条在本族里**只流向一处**——
`:1230` 的 `StrictWindow.hbase_of_cone_halfStrip_of_hmono_of_argmax hSwgen ha₀ hconv …`
（`:1150` 的非 shear 版同理），产出的就是 `hbase`。两股互不相干，所以扫掠窗口与结论集合
可以是两个 `Finset`。

**代价，写明白**：`hSwgen : IsGeneratingSet ξ Sw` 是**占位**，不是终局。原文 `:792` 说
`𝒮_{φ_ι}` 生成的是 `η − η̄_{ι₀}`（Lemma 2.5），**不是 `ξ`**；回到 `T^u η` 要靠 `:790`
那句「`η̄_{ι₀}` 沿平行 `ℓ` 的向量周期」（链上兑现物 `exists_zsmul_vl_mem_Per_eta`，本文件已证）
把差项消掉。这一步转移**仍然欠着**，只是从「`hstrict` 悄悄地对 `S` 为假」变成了
「`hSwgen` 对 `𝒮_{φ_ι}` 明着不成立」——**债没变小，但它现在有名字、有类型、挡不住
洞 3/5/6 三条几何义务并行推进**，而那三条在挂到 `Sw` 上之后是真陈述。
落地转移时本族签名会再动一次：`hSwgen` 换成「`Sw` 生成 `η − η̄_{ι₀}`」＋「差项 `vl`-周期」的配对。

---

🔴 **2026-09-20 停线警告（已处置，保留原文）：`hstrict` 挂错了集合，这条定理在预期实例上很可能是空真。**
在补上下面这个窗口集合之前，**不要**再对着本条的 `hcone` / `hstrip` / `hstrict` 派几何义务。

原文有**三个**不同的集合，我们只形式化了两个：

| 原文 | 出处 | 性质 | 链上对应物 |
|---|---|---|---|
| `𝒮_φ` | `:764`, `:777` | φ 的 Newton 多边形；边方向枚举出 `ℓ_1…ℓ_{2m}`；`B` 是 `E(𝒮_φ)`-包络 | `d.toDecompData.Sphi` ✔ |
| `𝒮` | `:774` | **η-生成集**（Lemma 2.4）；Lemma 2.3 保证它**有**一条平行 `ℓ` 的边和一条平行 `-ℓ` 的边 | 本条的 `S`（`hSgen`）✔ |
| `𝒮_{φ_ι}` | `:790-792` | `φ_ι(X) := ∏_{i≠ι₀}(X^{h_i}-1)` 的 Newton 多边形；是 **`η - η̄_{ι₀}`-生成集**；Lemma 2.6 保证它**没有**任何平行 `±ℓ` 的边 | 本条的 `Sw`（`hSwgen`，2026-09-20 加）🟡 占位 |

`hstrict : ∀ z ∈ Sw.erase a₀, ⟪nℓ, a₀⟫ < ⟪nℓ, z⟫` 配 `hperp : ⟪nℓ, vl⟫ = 0` 说的正是
「窗口集的 `nℓ`-极小面是单点」＝「窗口集没有平行 `ℓ` 的边」。**这恰恰是 `:774` 对 `𝒮` 否定的那件事**
（`|𝒮 ∩ ℓ_𝒮| ≤ |𝒮 ∩ -ℓ_𝒮|` 这句话本身就预设两条边各自非空），所以挂在 `S` 上时它为假。
「没有平行 `±ℓ` 的边」在原文里属于 `𝒮_{φ_ι}`，理由是 **Lemma 2.6**，不是 Lemma 2.3。
链上已有该理由的兑现物：`Nivat.Colle36.generatingSet_no_edge_parallel`（`Claim36.lean:749`），
结论 `∀ n ∈ E ↑S_ψ, ⟪n, ℓ_m⟫ ≠ 0`。

**所以扫掠窗口应当是 `𝒮_{φ_ι}` 而不是 `S`。** `S` 在 `WedgeResidualR`（`L1Claim.lean:928`）里
只出现在 `hline` / `hstraddle` 的 `derivedQ ε u' (S.image (· + v))` 里；**`hbase` 字段完全不提 `S`**，
所以换窗口不影响结论形状。真正欠的是原文 `:790-794` 的那一步转移：
`Ŝ_{φ_ι}` 生成的是 `η - η̄_{ι₀}`（Lemma 2.5），要回到 `T^u η` 需要 `η̄_{ι₀}` 在该区域上沿 `ℓ` 周期
（`:790` 那句 "Note that `η̄_{ι₀}` and then `(T^u(η-η̄_{ι₀}))|H_B(ℓ)` is periodic …"）。
mod-`p` 分解的机器已在链上：`AlphabetReduction.lean:282-288`；`L1Base.lean:245` 已记下
「`φ_ι ∈ ann_{ℤ_p}(η - η̄_{ι₀})` 需要 `R = ZMod p`」这条。

立案见 `blueprint/OPEN.md #15`。 -/
theorem wedgeResidualR_of_case1_of_cone_at_base
    {e : ℤ × ℤ} (hξ : IsMinimalCounterexample ξ) (d : DecompDataZ ξ)
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S) (hS : S.Nonempty)
    {Sw : Finset (ℤ × ℤ)} {a₀ : ℤ × ℤ}
    {B : Set (ℤ × ℤ)} {u' nℓ : ℤ × ℤ} {c cz : ℤ}
    -- 🔴 2026-09-21 集成者：`GeneratesAt ξ Sw a₀` 换成原文 `:786`+`:790`+`:792` 的捆绑形状。
    -- 原文从未断言 `𝒮_{φ_ι}` 生成 `ξ` 本身，只断言它在 `ZMod p` 里生成差 `η − η̄_{ι₀}`。
    (hSwgen : Nivat.SweepLines.ReducedGeneratesAt ξ Sw a₀ (c • vl))
    (ha₀ : a₀ ∈ Sw) (hconv : Nivat.LatticeConvex (Sw.erase a₀))
    (henv : Nivat.LE2.EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) B)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hc : 0 < c) (hvl_prim : Primitive vl)
    (hD : ∀ z ∈ Nivat.LE2.halfStrip B vl, (T e ξ) z = T (c • vl) (T e ξ) z)
    (hperp : Nivat.LE2.dot nℓ vl = 0)
    (hnu : Nivat.LE2.dot nℓ u' = -1)
    (hstrict : ∀ z ∈ Sw.erase a₀, Nivat.LE2.dot nℓ a₀ < Nivat.LE2.dot nℓ z)
    (hprim : Nivat.LE2.Prim nℓ) (i : Fin d.toDecompData.m)
    (hdoth : Nivat.LE2.dot nℓ (d.toDecompData.h i) = 0)
    (hcz : ∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b)
    (hczmem : ∃ b ∈ B, Nivat.LE2.dot nℓ b = cz)
    (hadj : ∀ n ∈ Nivat.LE2.E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)),
      ¬ (Nivat.LE2.dot n vl < 0 ∧ 0 < Nivat.LE2.dot n u'))
    (hcone : ∀ w ∈ Nivat.ConeRegion.coneRegion B vl u',
      Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ Sw.erase a₀, Nivat.LE2.dot nℓ (z + (w - a₀)) < cz →
        z + (w - a₀) ∈ Nivat.ConeRegion.coneRegion B vl u')
    (hstrip : ∀ w ∈ Nivat.ConeRegion.coneRegion B vl u',
      Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ Sw.erase a₀, cz ≤ Nivat.LE2.dot nℓ (z + (w - a₀)) →
        z + (w - a₀) ∈ Nivat.LE2.halfStrip B vl)
    {a : ℤ × ℤ} (ha : a ∈ d.toDecompData.Sphi)
    (hcorner : ∀ b ∈ d.toDecompData.Sphi,
      0 ≤ Nivat.LE2.dot (expNormal u' vl) (b - a) ∧
        0 ≤ Nivat.L1Line0.uCoord u' vl a b) :
    Nonempty (L1Claim.WedgeResidualR ξ S vl) := by
  have hz : Nivat.LE2.shift (-((0 : ℕ) • vl : ℤ × ℤ)) B = B := by
    ext z; simp [Nivat.LE2.shift]
  refine wedgeResidualR_of_case1_of_cone (e := e) hξ d hSgen hS hSwgen ha₀ hconv henv hBfin hBne
    hunimod hc hvl_prim 0 ?_ hperp hnu hstrict hprim i hdoth hcz hczmem hadj ?_ ?_ ha hcorner
  · simpa only [Nat.cast_zero, zero_smul, neg_zero, Nivat.LE2.shift, sub_zero,
      Set.setOf_mem_eq] using hD
  · simpa only [Nat.cast_zero, zero_smul, neg_zero, Nivat.LE2.shift, sub_zero,
      Set.setOf_mem_eq] using hcone
  · simpa only [Nat.cast_zero, zero_smul, neg_zero, Nivat.LE2.shift, sub_zero,
      Set.setOf_mem_eq] using hstrip

/-- **`η̄_ι` 沿 `ℓ` 周期——原文 `:790` 那句注记，链上已经免费**（接链第五轮，2026-09-20）。

`b3_colle2.txt:790`：*"Note that `η̄_{ι₀}` and then `(T^u(η − η̄_{ι₀}))|_{H_B(ℓ)}` is periodic
with period parallel to `ℓ`"*。这句话是 `:790-804` 那步转移的第一个零件，
而 `OPEN.md #15` 把整步转移记成了欠账。**本条说明第一个零件不欠：它由链上已有的
binder 直接产出，一行几何都不用新证。**

理由逐条：`hprim : Prim nℓ` 给 `nℓ ≠ 0`；`hperp : ⟪nℓ, vl⟫ = 0` 与
`hdoth : ⟪nℓ, h i⟫ = 0` 说 `vl` 与 `h i` 同时正交于同一个非零向量，故
`det vl (h i) = 0`（`Nivat.LE2.det_eq_zero_of_dot_eq_zero`，`LatticeEdges.lean:109`）；
`vl` 本原故 `h i = c • vl`（`Nivat.eq_zsmul_of_det_eq_zero`，`Lattice/Primitive.lean`）；
`h_ne` 给 `c ≠ 0`；而 `h_period : h i ∈ Per (eta i)`（`DecompData.lean:98`）**本来就是**
「`h i` 是 `η_i` 的周期」。合起来：`η_i` 沿 `vl` 方向有一个非零周期。

⚠ **这不是整步转移。** 还欠的是 `:792` 的 `𝒮_{φ_ι}` 生成 `η − η̄_{ι₀}`（Lemma 2.5，需要
`R = ZMod p`，`L1Base.lean:245` 已记）与 `:804` 的回传。本条只把「第一个零件是否欠」
这个问题关掉，免得 `#15` 的代价被高估。

`hperp` / `hprim` / `hdoth` / `hvl_prim` **四条都已经是**
`wedgeResidualR_of_case1_of_cone_at_base` 的 binder（`:3184`、`:3187`、`:3188`、`:3182`），
所以本条在那条定理的前提下是无条件可用的。 -/
theorem exists_zsmul_vl_mem_Per_eta (d : DecompDataZ ξ) {nℓ : ℤ × ℤ}
    (hprim : Nivat.LE2.Prim nℓ) (hvl_prim : Primitive vl)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (i : Fin d.toDecompData.m)
    (hdoth : Nivat.LE2.dot nℓ (d.toDecompData.h i) = 0) :
    ∃ c : ℤ, c ≠ 0 ∧ d.toDecompData.h i = c • vl ∧
      c • vl ∈ Per (d.toDecompData.eta i) := by
  have hdet : det vl (d.toDecompData.h i) = 0 :=
    Nivat.LE2.det_eq_zero_of_dot_eq_zero hprim.ne_zero hperp hdoth
  obtain ⟨c, hc⟩ := Nivat.eq_zsmul_of_det_eq_zero hvl_prim hdet
  have hcne : c ≠ 0 := by
    rintro rfl
    exact d.toDecompData.h_ne i (by rw [hc, zero_smul])
  exact ⟨c, hcne, hc, hc ▸ d.toDecompData.h_period i⟩

/-- **Lemma 2.6 接到链上的 `d` 与 `vl` 上**（接链第五轮，2026-09-20）。

`b3_colle2.txt:792`：*"Lemma 2.6 implies that `𝒮_{φ_ι}` does not have any edge parallel to
`−ℓ` or `ℓ`"*。链上兑现物是 `Nivat.Colle36.generatingSet_no_edge_parallel`
（`Claim36.lean:746`），但它的 `hℓ_dir : ∃ c ≠ 0, h i_m = c • ℓ_m` 一直没有生产者。

**`exists_zsmul_vl_mem_Per_eta`（上一条）正好就是那个生产者。** 于是这条 Lemma 2.6 的
结论在链上的 binder 下无条件成立，`hh_ne` / `hh_dir` 由 `DecompData` 的字段直接给
（`DecompData.lean:97`、`:104`）。

结论 `∀ n ∈ E ↑S_ψ, ⟪n, vl⟫ ≠ 0` **正是 `OPEN.md #15` 说 `𝒮_{φ_ι}` 有、而 `𝒮` 没有的那条性质**
（`:774` 保证 `𝒮` 恰恰**有**平行 `±ℓ` 的边）。它也正是
`Nivat.NoEdgePlacement` 那条严格 argmin 引理所要的 `hnoedge`。

🔴 **2026-09-20 订正：上一版这里写的「`hm : 2 ≤ d.m` 是 binder，不是推论，全树找不到
生产者」是错的，逐字撤回如下（`PROTOCOL.md` §14）。**

> ⚠ **`hm : 2 ≤ d.m` 是 binder，不是推论。** 全树找不到 `2 ≤ m` 的生产者
> （`grep '2 ≤ .*\.m'` 只命中 `ANormal.lean:484` 的 `d.m = 2` 假设）。同一条 `hm`
> 也是 `PosArea (↑d.Sphi)` 的唯一缺口（`m = 1` 时 `𝒮_φ` 是线段，`PosArea` 为假）——
> **两笔债是同一笔**，已派 Ahat 去 `b3_colle2.txt` 找出处。

**`2 ≤ m` 从来就不缺：它是 `DecompData` 自己的字段** `hm : 2 ≤ m`（`DecompData.lean:88`，
docstring「At least 2 components (needed for the argument)」），由
`DecompDataZ.of_minimalCounterexample`（`DecompData.lean:279`）证出。写法是
`d.toDecompData.hm`。原文出处 `b3_colle2.txt:424`（Lemma 3.5 的前提），`:379` 另行处理
`m = 1`。

上一版的 grep 之所以落空，是因为在 `structure` 内部这个字段写作 `hm : 2 ≤ m`——
**没有投影点**，`'2 ≤ .*\.m'` 这个模式匹配不到。**这是硬规矩 3 的实例：
「找不到生产者」这句话写进文件之前，必须先 `#check` 一次**（`#check
fun {α} [AddCommMonoid α] {η : Config α} (d : Nivat.Colle35.DecompData η) => d.hm`
几秒钟的事）。由此 `posArea_Sphi`（`AhatMono.lean:3173`）也已经是**无条件**的。

⚠ **本条不解决 `#15`。** 还欠 `:792` 的 Lemma 2.5 一侧（`𝒮_{φ_ι}` 生成的是
`η − η̄_{ι₀}`，需要 `R = ZMod p`；机器在 `AlphabetReduction.exists_prime_colle_reduction`）
与 `:804` 的回传。本条关掉的是「Lemma 2.6 这一侧欠不欠」。 -/
theorem no_edge_parallel_vl_of_erase (d : DecompDataZ ξ) {nℓ : ℤ × ℤ}
    (hm : 2 ≤ d.toDecompData.m)
    (hprim : Nivat.LE2.Prim nℓ) (hvl_prim : Primitive vl)
    (hperp : Nivat.LE2.dot nℓ vl = 0) (i : Fin d.toDecompData.m)
    (hdoth : Nivat.LE2.dot nℓ (d.toDecompData.h i) = 0)
    {S_ψ : Finset (ℤ × ℤ)}
    (hS_hull : Conv S_ψ = Conv (supp (∏ j ∈ Finset.univ.erase i,
      (mono (d.toDecompData.h j) - 1 : LaurentTwo ℤ)))) :
    ∀ n ∈ Nivat.LE2.E (↑S_ψ : Set (ℤ × ℤ)), Nivat.LE2.dot n vl ≠ 0 := by
  obtain ⟨c, hcne, hc, -⟩ :=
    exists_zsmul_vl_mem_Per_eta d hprim hvl_prim hperp i hdoth
  exact Nivat.Colle36.generatingSet_no_edge_parallel hm d.toDecompData.h_ne
    d.toDecompData.h_dir hvl_prim ⟨c, hcne, hc⟩ hS_hull

/-- **`hD` 与 `c` 一起消掉**（接链第五轮，2026-09-20）。

🟠 **2026-09-20 晚：本条及其上游四条装配器（`wedgeResidualR_of_cone_hmono_at_shear`、
`_of_cone_hmono_at_shear_of_argmax`、`_of_cone_of_enveloped`、`_of_case1_of_cone`、
`_of_case1_of_cone_at_base`）已被 `exists_wedgeResidualR` 停用**，改走两阶段路线
（`claim46_of_case1` → `exists_stage2_frame_of_claim46` → `wedgeResidualR_of_stage2_frame`）。
🔴 **2026-09-21 再订正**：那条两阶段路线本身也已退役（`OPEN.md #21`），现走
`claim46_of_case1` → `exists_cutResidualR_of_claim46` → `L1Claim.exists_L1MaxBResidual_of_cutResidualR`。
停用的理由不是证明有错——五条全部 0 sorry、`#print axioms` 干净——而是**签名把
`hadj` 与 `hcorner` 绑在同一个 `(vl, u')` 上**，`CornerAdjClash.det_eq_zero_of_adj_of_corner`
证明那样绑迫使 `m ≤ 2`。按 `PROTOCOL.md` §14 **保留不删**：它们记着「两条各自公理干净的
引理仍可能无法合成」这条教训，且 `hD`/`c` 的消法（下面这段）在新路线里被
`claim46_of_case1` 逐字复用。

`wedgeResidualR_of_case1_of_cone_at_base` 的 `hD` 说的是「`T e ξ` 在 `halfStrip B vl` 上
`c • vl`-周期」。原文 `:778` 给的**不是**这句，而是 Case 1 的定义式
「`(T^u η)|_{H_B(ℓ)} = x_per|_{H_B(ℓ)}`」——即与周期构型 `xper` 在半带上**逐点相等**。
两者差一步：相等把 `xper` 的周期搬过来，而 `halfStrip B vl` 对 `+ c • vl`（`0 ≤ c`）封闭。

链上兑现物早已存在且干净，只是从来没人接：
* `Nivat.L1Line0.exists_pos_zsmul_mem_Per`（`L1Line0.lean:504`）——由 `hvl_prim` / `hp_mem` /
  `hp_ne` / `hdet_vl` 产出 `∃ c, 0 < c ∧ c • vl ∈ Per xper`。`det p vl = 0` 配 `vl` 本原给
  `p = c₀ • vl`，`Per` 是子群故可取正倍数。**团队的 `0 < c` 约定就是从这里免费来的。**
* `Nivat.L1Line0.hD_of_agree_halfStrip`（`L1Line0.lean:518`）——逐点相等 + 周期 ⟹ `hD`。

因为结论 `Nonempty (L1Claim.WedgeResidualR ξ S vl)` **不提 `c`**，`c` 可以就地存在化。
于是本条的 binder 列表比上一条**少三个**（`c`、`hc`、`hD`），换来的四个
（`hu`、`hp_mem`、`hp_ne`、`hdet_vl`）全部是 `exists_decompDataZ`（`:490-493`）已经在
产出的东西：`p ∈ Per xper ∧ p ≠ 0 ∧ vl ≠ 0 ∧ Primitive vl ∧ det p vl = 0` 逐字在那条的
结论里，`hu` 就是 Case 1 本身。**净减三条义务，且减掉的是几何债那一栏。**

原文：b3_colle2.txt:778（Case 1 的定义式）。

✅ **不受 `blueprint/OPEN.md #15` 影响**：`hD` 整条不提窗口集合 `S`，`#15` 换的是 `hstrict` /
`hcone` / `hstrip` 挂的那个集合。本条的 `hstrict` 仍原样传给上一条，停线警告照旧对它有效。 -/
theorem wedgeResidualR_of_case1_of_cone_at_base_of_agree
    {e : ℤ × ℤ} (hξ : IsMinimalCounterexample ξ) (d : DecompDataZ ξ)
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S) (hS : S.Nonempty)
    {Sw : Finset (ℤ × ℤ)} {a₀ : ℤ × ℤ}
    -- 🔴 2026-09-21 集成者：同 `claim46_of_case1`，`c` 不是 binder，用 `:790` 的方向形。
    (hSwgen : Nivat.SweepLines.ReducedGeneratesAtDir ξ Sw a₀ vl)
    (ha₀ : a₀ ∈ Sw) (hconv : Nivat.LatticeConvex (Sw.erase a₀))
    {B : Set (ℤ × ℤ)} {u' nℓ : ℤ × ℤ} {cz : ℤ}
    (henv : Nivat.LE2.EnvOf (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) B)
    (hBfin : B.Finite) (hBne : B.Nonempty)
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hvl_prim : Primitive vl)
    (hu : ∀ z ∈ Nivat.LE2.halfStrip B vl, T e ξ z = xper z)
    (hp_mem : p ∈ Per xper) (hp_ne : p ≠ 0) (hdet_vl : det p vl = 0)
    (hperp : Nivat.LE2.dot nℓ vl = 0)
    (hnu : Nivat.LE2.dot nℓ u' = -1)
    (hstrict : ∀ z ∈ Sw.erase a₀, Nivat.LE2.dot nℓ a₀ < Nivat.LE2.dot nℓ z)
    (hprim : Nivat.LE2.Prim nℓ) (i : Fin d.toDecompData.m)
    (hdoth : Nivat.LE2.dot nℓ (d.toDecompData.h i) = 0)
    (hcz : ∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b)
    (hczmem : ∃ b ∈ B, Nivat.LE2.dot nℓ b = cz)
    (hadj : ∀ n ∈ Nivat.LE2.E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)),
      ¬ (Nivat.LE2.dot n vl < 0 ∧ 0 < Nivat.LE2.dot n u'))
    (hcone : ∀ w ∈ Nivat.ConeRegion.coneRegion B vl u',
      Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ Sw.erase a₀, Nivat.LE2.dot nℓ (z + (w - a₀)) < cz →
        z + (w - a₀) ∈ Nivat.ConeRegion.coneRegion B vl u')
    (hstrip : ∀ w ∈ Nivat.ConeRegion.coneRegion B vl u',
      Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ Sw.erase a₀, cz ≤ Nivat.LE2.dot nℓ (z + (w - a₀)) →
        z + (w - a₀) ∈ Nivat.LE2.halfStrip B vl)
    {a : ℤ × ℤ} (ha : a ∈ d.toDecompData.Sphi)
    (hcorner : ∀ b ∈ d.toDecompData.Sphi,
      0 ≤ Nivat.LE2.dot (expNormal u' vl) (b - a) ∧
        0 ≤ Nivat.L1Line0.uCoord u' vl a b) :
    Nonempty (L1Claim.WedgeResidualR ξ S vl) := by
  obtain ⟨c, hc, hper⟩ :=
    Nivat.L1Line0.exists_pos_zsmul_mem_Per hvl_prim hp_mem hp_ne hdet_vl
  obtain ⟨c₀, hc₀, hR⟩ := Nivat.SweepLines.reducedGeneratesAt_of_dir hSwgen
  have hper' : (c * c₀) • vl ∈ Per xper := by
    have h : (c * c₀) • vl = c₀ • (c • vl) := by rw [mul_comm, mul_smul]
    rw [h]
    exact AddSubgroup.zsmul_mem _ hper c₀
  exact wedgeResidualR_of_case1_of_cone_at_base (e := e) (c := c * c₀) hξ d hSgen hS (hR c)
    ha₀ hconv
    henv hBfin hBne hunimod (mul_pos hc hc₀) hvl_prim
    (Nivat.L1Line0.hD_of_agree_halfStrip hu (mul_pos hc hc₀).le hper')
    hperp hnu hstrict hprim i hdoth hcz hczmem hadj hcone hstrip ha hcorner

/-- **`hcz` / `hczmem` 是免费的**（接链第四轮，2026-09-20）。

`wedgeResidualR_of_case1_of_cone_at_base` 的两条新前提 `hcz` / `hczmem` 合起来说的是
「`cz` 是 `B` 在 `nℓ` 方向上的最低层，且这一层非空」。对有限非空的 `B` 这永远可取——
取 `nℓ`-argmin 即可。所以把 `hlean` 换成 `hcz`/`hczmem`/`hadj` 之后，**真正新增的义务只有
`hadj` 一条**（`b3_colle2.txt:764` 的相邻性）。

原文：`b3_colle2.txt:796`「`l₁ := ℓ_B^{(-)}`」——`cz` 就是这条切割线的层号。 -/
theorem exists_cutLevel {B : Set (ℤ × ℤ)} (hBfin : B.Finite) (hBne : B.Nonempty)
    (nℓ : ℤ × ℤ) :
    ∃ cz : ℤ, (∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b) ∧ ∃ b ∈ B, Nivat.LE2.dot nℓ b = cz := by
  have hFne : hBfin.toFinset.Nonempty := by
    obtain ⟨b, hb⟩ := hBne
    exact ⟨b, hBfin.mem_toFinset.mpr hb⟩
  obtain ⟨b0, hb0F, hb0min⟩ :=
    hBfin.toFinset.exists_min_image (fun z => Nivat.LE2.dot nℓ z) hFne
  refine ⟨Nivat.LE2.dot nℓ b0, ?_, b0, hBfin.mem_toFinset.mp hb0F, rfl⟩
  intro b hb
  exact hb0min b (hBfin.mem_toFinset.mpr hb)
-- 2026-09-22：`exists_nℓ_and_index_of_oneSided` 搬到 `LineGenIndex.lean`（leaf A 组装文件也要用）。



/-- **L1's residual as data: the wedge bundle `L1Claim.WedgeResidualR`** (`L1Claim.lean:928`).

**2026-09-19 20:5x — this is the wiring action, not new mathematics.**  `exists_L1MaxBResidual`
below now has a `sorry`-free body: it is `L1Claim.exists_L1MaxBResidual_of_wedgeResidualR`
(`L1Claim.lean:957`, kernel-clean) applied to this declaration.  `sorry TOTAL` is unchanged at
two and so is `axiom_closure`; per `CLAUDE.md` hard rule 1 **that means zero progress**.  What
it buys is the one thing the L1 tree had never had:

> Before this, `grep -rln "Colle.L1Claim" Nivat/` returned `All.lean` and nothing else.
> `L1Claim` and its 96-module `import` closure were kernel-verified, `sorry`-free, and
> **unreachable from `nivat_conjecture`** — the exact shape `CLAUDE.md` records for `L1Data`
> and `L1Assemble` before each of them was wired.  Wiring is an independent landing action; it
> does not happen because more lemmas accumulate.

**The obligation is now eight data fields and six proof fields, not an opaque `∃`.**
`WedgeResidualR ξ S vl` asks for `e u' v b₀ c ε B k` together with `hb₀ : b₀ ∈ B`,
`hunimod : det u' vl = ±1`, `c0 : c ≠ 0`, `hconv`, `hbase`, `hline`, `hstraddle`.  Three of
those six are already discharged for free on the intended route and should never be attacked
directly:

* `hconv` is **free from `hunimod`** — `L1LevelSpan.isLatticeConvexRegion_wedgeFull_of_unimod'`
  holds for *any* `B`, which is why `hlev` was shown redundant and `OPEN.md #10 / #12` closed.
* `hline` / `hstraddle` are the `L1Straddle*` chain's targets.

so the live content is **`hbase` alone** — `OPEN.md #13`, whose two walls are both pinned to
kernel `iff`s already (`HbaseBridge.not_cutBand_subset_wedgeFull_iff` on the flat `hwin` route,
`L3Band.chainFull_succ_subset_genClosure_iff_of_ahead` (`L3Band.lean:4074`) on the corner-vertex
route).

⚠ **Reading limit, stated because no bridge goes back.**  `exists_L1MaxBResidual_of_wedgeResidualR`
is a one-way implication, so this statement is *a priori* **at least as strong** as the one it
replaces: a bundle yields the residual, but nothing here derives a bundle from the residual.
If some future `WedgeResidualR`-free route to `MaxBResidual` appears, this declaration is the
thing to re-examine, not the thing to cite.  The strengthening is deliberate and is the route
every landed L1 lemma is built for; it is **not** measured to be equivalent.

🔴 **2026-09-20 — the paragraph above beginning "so the live content is `hbase` alone" is
retracted, kept per `PROTOCOL.md` §14.**  It was true of the `HwinHoleZ` route, and that route
is refuted (`L1SweepBridge.not_hwinHoleZ_of_case1`, `:1604`) from binders this theorem already
has.  The body comment below states what replaced it and why the refutation is of *our*
encoding — a `∀ K` and a lexicographic row/column prefix, neither of which occurs in
`b3_colle2.txt:792-804` — rather than of Collé's argument.  The `hconv`-is-free and
`hline`/`hstraddle`-are-`L1Straddle*` remarks above are unaffected; only the "`hbase` alone"
reduction is withdrawn.

🔴 **2026-09-21 — renamed from `exists_wedgeResidualR` and its conclusion changed**
(`OPEN.md #21`; the old name is kept in this sentence so that `grep exists_wedgeResidualR`,
which still hits ~20 docstrings elsewhere, lands here).  The conclusion is now
`Nonempty (L1Claim.CutResidualR ξ S vl)` — Collé's own `𝓡^n_I` (`b3_colle2.txt:818`,
half-plane cuts of `𝓡_{I-1}` along `ℓ' = ℓ_I`, growing along `v⃗_{ℓ_{I-1}}`) rather than the
quadrant `chainFull B vl u₂ b₀ k`, whose layers are exposed along `-vl` and which therefore
matches the paper only at the top of the tower `:812`.  **Stage 1 of the body is unchanged**;
only the last `exact` moved.  Everything about `WedgeResidualR` above this line describes the
retired route and is kept per `PROTOCOL.md` §14. -/
theorem exists_cutResidualR
    (hξ : IsMinimalCounterexample ξ) (d : DecompDataZ ξ)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_pos : Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hxper : xper ∈ orbitClosure ξ) (hgen : Nivat.Colle.GeneratesAt ξ S gen)
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (hp_mem : p ∈ Per xper) (hp_ne : p ≠ 0) (hvl_ne : vl ≠ 0) (hvl_prim : Primitive vl)
    (hdet_vl : det p vl = 0) (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0)
    (hdef : ∀ (n : ℝ × ℝ) (cmax cmin : ℝ),
      (∀ z ∈ S, inner2 n z ≤ cmax) → (Nivat.R2.face S n cmax).Nonempty →
      (∀ z ∈ S, cmin ≤ inner2 n z) → (Nivat.R2.face S n cmin).Nonempty →
        P ξ S - P ξ (S.filter fun z => inner2 n z < cmax) ≤
          (Nivat.R2.face S n cmax).card - 1 ∧
        P ξ S - P ξ (S.filter fun z => cmin < inner2 n z) ≤
          (Nivat.R2.face S n cmin).card - 1)
    (hcase1 : Case1 ξ xper d.Sphi vl) :
    Nonempty (L1Claim.CutResidualR ξ S vl) := by
  -- 🔴 **2026-09-20: the `HwinHoleZ` reduction was backed out, because it is refuted.**
  --
  -- Until this edit the body read
  --     `refine L1SweepBridge.wedgeResidualR_of_hwinHoleZ hξ d hSgen hcase1 hvl_prim hp_mem`
  --     `  hp_ne hdet_vl ?_ ; sorry`
  -- so the `sorry`'s goal was `HwinHoleZ ξ d.Sphi vl`, advertised as "one named proposition".
  -- That proposition is **false at every Case 1 instance**:
  -- `L1SweepBridge.not_hwinHoleZ_of_case1` (`:1604`) proves `¬ HwinHoleZ ξ d.Sphi vl` from
  -- `d hcase1 hvl_prim hp_mem hp_ne hdet_vl` — **every one of which is bound right here**.
  -- So the old body reduced this theorem to a goal that is refutable from the binders in scope:
  -- a `sorry` that can never be discharged, presented as progress.  Backing out costs nothing
  -- measurable (`sorries.sh` still says 2) and makes the remaining hole say something true.
  --
  -- **Why the reduction was false — it is our encoding, not Collé's argument.**  Two features
  -- of `HwinHoleZ` have no counterpart in the source, and both are load-bearing in the
  -- refutation (hard rule 7 in `CLAUDE.md`, added because of this):
  --
  -- 1. `∀ K` — "for *every* shear `u' - K • vl`".  `b3_colle2.txt:792-804` quantifies no shear
  --    at all.  `not_hwinHoleZ_of_case1` wins by driving `K` unbounded
  --    (`not_exists_enum_hwin_hK_of_shear`, `hKpos : 2*Mn + 2 ≤ K`) and contradicting `hamin`
  --    there; with one fixed `u'` there is nothing to unbound.
  -- 2. The `enum : ℕ → ℕ → ℤ × ℤ` **row/column double index with a lexicographic prefix**
  --    (`enum i '' {j' | j' < j}` — inside row `i`, only the strict prefix is available).  This
  --    is inherited from `HbaseBridge.hbase_at_of_sweep_of_isGeneratingSet` (`:185`).  Collé's
  --    induction is over **lattice lines only**: `A₁ := 𝓡_{ι-1} ∩ l₁` with `l₁ := ℓ_B^{(-)}`,
  --    and periodicity is extended to *all of* `A₁` in one step ("the knowledge of `T^u η` on
  --    `H_B(ℓ)` determines uniquely `T^u η` on `A₁`", Figure 10), then `l₂ := l₁^{(-)}`, "and
  --    proceeding this way, we get by induction".  There is **no order inside a line**, because
  --    each point of `A_i` is determined from `H_B(ℓ) ∪ A_1 ∪ … ∪ A_{i-1}` independently —
  --    Lemma 2.6 gives `𝒮_{φ_ι}` no edge parallel to `±ℓ`, hence a *unique* extreme vertex,
  --    hence exactly one point of each placed translate sticking past the line.
  --    `not_hwin_of_row_zero_levelConst` kills the prefix version precisely by taking row 0
  --    infinite and level-constant, so no point at a different level is available in the
  --    prefix.  Under Collé's shape step `i` holds *all* of `A_{i-1}`, whose levels differ, and
  --    the obstruction has nothing to bite.
  --
  -- **The replacement is being built, not assumed**: `SweepLines.lean` (line-indexed engine),
  -- `NoEdgePlacement.lean` (unique extreme vertex from "no parallel edge"), `SweepBase.lean`
  -- (the `i = 0` containment, which may well need `B` to contain Collé's box `[-i+1,i-1]²` from
  -- item (ii), `b3_colle2.txt:474`).  Until one of those lands, this hole is the whole bundle
  -- again and this comment is the honest statement of that.
  --
  -- ⚠ Do **not** re-narrow this to `HwinHoleK` (`HwinHoleK.lean:44`, `∀ K` → `∃ K`).  That is
  -- the same invention with a different quantifier, not the source's statement; hard rule 7's
  -- corollary names it explicitly.
  --
  -- ═══ 骨架精化（2026-09-20，用户裁决「允许，但只限集成者之手」）═══
  --
  -- 下面把一个 80 行的不可分 `sorry` 换成 **6 个具名洞**，每个洞都是一条独立陈述，
  -- 都在链上（它们是一个**今天就通过类型检查**的证明项里的 `have`），
  -- 且消费者就是下面那一行 `exact`。派工时点一个 `have` 即可，
  -- 不再需要回答硬规矩 9 的「谁消费它」——目标本身就是链上证明项里的一个洞。
  --
  -- **`sorry` 数从 1 升到 6 是这次编辑的目的，不是副作用。** 人类做 Lean 的标准动作是
  -- 分解期抬高 `sorry`、填坑期降下来，形状是驼峰不是斜坡。原来那条 `sorry` 不可并行攻，
  -- 因为它没有名字；这 6 条可以。`axiom_closure` 不变（硬规矩 1：这本身不算进度）。
  --
  -- **免费的部分**（不占洞，已由内核给出）：`hcase1` 直接给出 `B`/`henv`/`e`/`hu` 四项；
  -- `hS` 是 `hSgen.1`；`hBne` 是 `L1Line0.nonempty_of_enveloped_Sphi`（`L1Line0.lean:639`）；
  -- `hBfin` 是 `L1Sfin.hSfin_of_decompDataZ`（`HbaseFlatSeed.lean:804` 的
  -- `exists_b₀_max_of_envOf` 用的就是这两条）；
  -- `cz`/`hcz`/`hczmem` 是本文件 `exists_cutLevel`（对有限非空 `B` 无条件）。
  classical
  obtain ⟨B, henv, e, hu⟩ := hcase1
  have hS : S.Nonempty := hSgen.1
  have hBne : B.Nonempty := Nivat.L1Line0.nonempty_of_enveloped_Sphi d henv
  have hBfin : B.Finite := Nivat.L1Sfin.hSfin_of_decompDataZ d B henv
  -- 洞 1：`ℓ` 的法向 `nℓ`，以及 `:788` 的指标选取 `ι₀ = ι mod m`。
  -- `hdoth` 那一条正是原文 `:788` 选 `ι₀` 的那句；配 `exists_zsmul_vl_mem_Per_eta`
  -- （本文件，已证）即得 `:790` 的「`η̄_{ι₀}` 以平行 `ℓ` 的向量为周期」。
  -- 🟢 **洞 1 已关闭**（2026-09-20）：`exists_nℓ_and_index_of_oneSided`（本文件，上方），
  -- 即原文 `:939` 的 Lemma 2.6 用在 `d.ann` 上；`ℓ ≠ 0` 由 `hℓ_nel` 的 `Primitive ℓ` 给出。
  obtain ⟨nℓ, hprim, hperp, hdetpos, i, hdoth⟩ :
      ∃ nℓ : ℤ × ℤ, Nivat.LE2.Prim nℓ ∧ Nivat.LE2.dot nℓ vl = 0 ∧ 0 < det nℓ vl ∧
        ∃ i : Fin d.toDecompData.m,
          Nivat.LE2.dot nℓ (d.toDecompData.h i) = 0 := by
    -- 2026-09-24（第 182 轮，集成者）：**定向 `0 < det nℓ vl` 在这里是免费的**
    -- （`PROTOCOL.md` §54 下半的「状态 2」）。`exists_nℓ_and_index_of_oneSided` 的三个合取
    -- 在 `nℓ ↦ -nℓ` 下逐条不变（`Prim.neg`；`dot` 齐次），而 `det nℓ vl ≠ 0` 由
    -- `det_ne_zero_of_dot_eq_zero`（本文件）从 `nℓ ≠ 0` + `vl ≠ 0` + `hperp` 得到，
    -- 所以两支里恰有一支是正的，取那一支即可。⟹ 消费者
    -- `exists_cutResidualR_of_claim46` 的 `hdetpos` binder **不是新债**。
    obtain ⟨n, hn, hnperp, i, hi⟩ :=
      exists_nℓ_and_index_of_oneSided d hℓ_pos hℓ_nel.1.ne_zero hvl_prim hdet_ℓ
    have hne : det n vl ≠ 0 :=
      det_ne_zero_of_dot_eq_zero hn.ne_zero hvl_prim.ne_zero hnperp
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · refine ⟨-n, hn.neg, ?_, ?_, i, ?_⟩
      · simp only [Nivat.LE2.dot, Prod.fst_neg, Prod.snd_neg] at hnperp ⊢
        linarith
      · simp only [det, Prod.fst_neg, Prod.snd_neg] at hlt ⊢
        linarith
      · simp only [Nivat.LE2.dot, Prod.fst_neg, Prod.snd_neg] at hi ⊢
        linarith
    · exact ⟨n, hn, hnperp, hgt, i, hi⟩
  -- 洞 2：锥的第二方向 `u'`。三条合取分别是幺模、`nℓ` 配对、以及 `:764` 的相邻性
  -- （`hadj`）。⚠ Wbox 本轮实测：剪切路线产不出 `hadj ∧ hcorner`（`hcorner` 对 `K` 上闭、
  -- `hmono`/`hadj` 下闭，只能交于 `K = 0`，而 `no_nonpos_shear_hmono` 排除 `K = 0`）。
  -- 所以这一条要在**未剪切的 `u'`** 上直接证，不要再走 shear。
  -- 🟢 **洞 2 已关闭**（2026-09-20，Wbox）：`Nivat.EnvFit.exists_cone_direction_adjacent_Sphi`
  -- （`EnvFit.lean:2755`），无新前提——`(E ↑𝒮_φ).Finite` 由 `finite_E_of_finite` 免费给出，
  -- `hunimod` 由 `hprim ∧ hperp` 自动（`exists_u'_of_perp`），`hadj` 由沿 `vl` 的下闭剪切
  -- （`exists_shear_adjacent_le`）把有限多条 `dot n vl < 0` 的边法向一次压到 `≤ 0`。
  obtain ⟨u', hunimod, hnu, hadj⟩ :
      ∃ u' : ℤ × ℤ, (det u' vl = 1 ∨ det u' vl = -1) ∧
        Nivat.LE2.dot nℓ u' = -1 ∧
        ∀ n ∈ Nivat.LE2.E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)),
          ¬ (Nivat.LE2.dot n vl < 0 ∧ 0 < Nivat.LE2.dot n u') :=
    Nivat.EnvFit.exists_cone_direction_adjacent_Sphi d hvl_prim hprim hperp
  obtain ⟨cz, hcz, hczmem⟩ := exists_cutLevel hBfin hBne nℓ
  -- 洞 3：**扫掠窗口集 `Sw` 及其 `nℓ`-严格极小点 `a₀`。`OPEN.md #15` 已裁决为 (B)。**
  --
  -- 🔴 这个洞上一版写的是 `∃ a₀ ∈ S, …`，**那个陈述在预期实例上为假**：
  -- `hstrict` 配 `hperp : ⟪nℓ, vl⟫ = 0` 说的正是「`S` 的 `nℓ`-极小面是单点」
  -- ＝「`S` 没有平行 `ℓ` 的边」，而原文 `:774` 对 `𝒮`（Lemma 2.4 的生成集，
  -- 即这里的 `S`）恰恰**断言有**这样的边（Lemma 2.3）。写成 `S` 就是把整条定理
  -- 归约到一个可证伪的目标——`HwinHoleZ` 那次犯的就是这个错（硬规矩 7）。
  --
  -- 裁决依据（我复核过 `L1Claim.lean:928` 的字段）：`S` 在 `WedgeResidualR` 里**只**出现在
  -- `hline` / `hstraddle` 的 `derivedQ ε u' (S.image (· + v))`，**`hbase` 整条不提 `S`**；
  -- 而 `hstrict` / `hcone` / `hstrip` 只用来造 `hbase`（经
  -- `StrictWindow.hbase_of_cone_halfStrip_of_hmono_of_argmax`）。所以扫掠窗口与结论集合
  -- 可以分开，五条装配器已按此改签名：新增 `{Sw}` + `hSwgen`，`ha₀`/`hconv`/`hstrict`/
  -- `hcone`/`hstrip` 全部挂到 `Sw` 上，`hSgen`/`hS` 留在 `S` 上。
  --
  -- **预期取值**：`Sw := 𝒮_{φ_ι}`，即 `φ_ι(X) = ∏_{j≠i}(X^{h_j} − 1)` 的 Newton 多边形
  -- （原文 `:790-792`）。它的「无平行 `±ℓ` 的边」来自 Lemma 2.6，链上兑现物是
  -- `no_edge_parallel_vl_of_erase`（本文件，已证）+
  -- `NoEdgePlacement.strict_argmin_of_generatingSet_no_edge_parallel`（已证）。
  --
  -- ⚠ **`hSwgen` 是这次裁决新暴露出来的真债，不是我发明的加强。** 原文 `:792` 说
  -- `𝒮_{φ_ι}` 是 `η − η̄_{ι₀}` 的生成集（Lemma 2.5，要 `R = ZMod p`），**不是 `ξ` 的**；
  -- 要回到 `T^u η` 得用 `:790` 那句「`η̄_{ι₀}` 沿平行 `ℓ` 的向量周期」把差项消掉
  -- （`exists_zsmul_vl_mem_Per_eta`，本文件已证，正是那句）。把它写成 `IsGeneratingSet ξ Sw`
  -- 是**暂时的占位**：它让三条几何义务（洞 3/5/6）立刻变成真陈述、可以并行攻，
  -- 而把 `:790-804` 的转移集中成这一条 binder。落地那一步时这条要换成
  -- 「`Sw` 生成 `η − η̄_{ι₀}` ＋ 差项 `vl`-周期」的配对，装配器签名会再动一次。
  -- Lemma 2.5 的 mod-`p` 机器已在链上：`AlphabetReduction.isGeneratingSet_psi_at_prime`。
  obtain ⟨Sw, hSwconv, hEsub, hSwzono, a₀, ha₀, hconv, hstrict, hSwgen⟩ :
      ∃ Sw : Finset (ℤ × ℤ),
        Nivat.LatticeConvex Sw ∧
        Nivat.LE2.E (↑Sw : Set (ℤ × ℤ)) ⊆
          Nivat.LE2.E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) ∧
        Nivat.Conv Sw = Nivat.Conv (Nivat.LE2.zonoF (Finset.univ.erase i) d.toDecompData.h) ∧
        ∃ a₀ ∈ Sw, Nivat.LatticeConvex (Sw.erase a₀) ∧
          (∀ z ∈ Sw.erase a₀,
            Nivat.LE2.dot nℓ a₀ < Nivat.LE2.dot nℓ z) ∧
          Nivat.SweepLines.ReducedGeneratesAtDir ξ Sw a₀ vl :=
    -- 🟢 **2026-09-21，集成者之手：洞 3 的 `hSwgen` 不再是占位，而是原文三句的实际装配。**
    --
    -- `b3_colle2.txt:786-792` 一共说了三件事，`ReducedGeneratesAtDir` 逐字捆绑这三件：
    --
    -- | 原文 | 出处 | 链上兑现物 |
    -- |---|---|---|
    -- | "let `p` be a prime such that `𝒜 ⊂ ℤ_p`" | `:786` | `exists_prime_injOn_intCast hξ.1.1` |
    -- | "`η̄_{ι₀}` is periodic with period parallel to `ℓ`" | `:790` | `exists_zsmul_vl_mem_Per_eta` |
    -- | "Lemma 2.5 states that `𝒮_{φ_ι}` is an `η − η̄_{ι₀}`-generating set" | `:792` | `exists_window_strict_at_prime` |
    --
    -- 三件都在链上、都 0 sorry。⚠ **原文从未断言 `𝒮_{φ_ι}` 生成 `ξ` 本身**——上一版写的
    -- `GeneratesAt ξ Sw a₀` 是我们自己加的（硬规矩 7 的债），它对预期见证明着为假，
    -- 所以按旧写法这条 `sorry` 不可能关掉。换成捆绑形之后它**关掉了**。
    --
    -- 🟡 **唯一残余：`hhull_mod`。** 那是一条纯代数陈述——`ψ := ∏_{j≠ι₀}(X^{h_j}−1)` 的
    -- Newton 多边形在 `ℤ` 与在 `ZMod p` 上重合。`ℤ` 那半已有
    -- `NewtonZonotope.Conv_supp_prod_eq_Conv_zonoF`（经 `ℂ`、Ostrowski），
    -- `ZMod p` 那半缺一条同型的 `newt_prod`（`Ostrowski.lean:171` 只对 `ℂ` 成立）。
    -- 它不含任何构型内容，是可以单独派出去的一条。
    by
      -- `:786`：`IsCounterexample` 的第一个合取就是 `(Set.range ξ).Finite`。
      obtain ⟨pp, hpp, hinj⟩ :=
        Nivat.Colle.AlphabetReduction.exists_prime_injOn_intCast hξ.1.1
      -- `:790`：`η̄_{ι₀}` 的周期平行于 `ℓ`；`Per` 是子群，故可取正倍数。
      obtain ⟨c₀, hc₀ne, -, hc₀per⟩ :=
        exists_zsmul_vl_mem_Per_eta d hprim hvl_prim hperp i hdoth
      obtain ⟨c₁, hc₁, hc₁per⟩ :
          ∃ c₁ : ℤ, 0 < c₁ ∧ c₁ • vl ∈ Per (d.toDecompData.eta i) := by
        rcases lt_trichotomy c₀ 0 with hneg | h0 | hpos
        · refine ⟨-c₀, by omega, ?_⟩
          simpa [neg_smul] using neg_mem hc₀per
        · exact absurd h0 hc₀ne
        · exact ⟨c₀, hpos, hc₀per⟩
      -- `:792`：Lemma 2.5 在 `ZMod p` 上的形态。
      obtain ⟨Sw, hgenSw, hSwconv, hEsub, hSwzono, a₀, ha₀, hconv_erase, hstrict⟩ :=
        Nivat.ColleReg.exists_window_strict_at_prime d d.toDecompData.hm hprim hvl_prim hperp
          i hdoth hpp
          (hhull_mod := fun Sw hhull =>
            haveI : Fact pp.Prime := ⟨hpp⟩
            Nivat.hhull_mod_of_prime _ _ (fun j _ => d.toDecompData.h_ne j) Sw hhull)
          (hnoedge := fun Sw hhull =>
            no_edge_parallel_vl_of_erase d d.toDecompData.hm hprim hvl_prim hperp i hdoth hhull)
      exact ⟨Sw, hSwconv, hEsub, hSwzono, a₀, ha₀, hconv_erase, hstrict,
        Nivat.SweepLines.reducedGeneratesAtDir_of_isGeneratingSet_sub hinj hc₁ hc₁per
          hgenSw ha₀ hconv_erase⟩
  -- **两条新增合取（2026-09-20，集成者之手）都由预期见证 `Sw := 𝒮_{φ_ι}` 免费满足**，
  -- 不是超出原文的加强：`:792` 把 `φ_ι(X) := ∏_{i≠ι₀}(X^{h_i}−1)` 定义成同一组生成元
  -- **去掉一个**之后的 zonotope，所以 (a) 它仍是 zonotope ⟹ `LatticeConvex Sw`；
  -- (b) 由 `Nivat.LE2.E_zono`（`MinkowskiEdges.lean:292`，`E` 是各 `E (segOf (h i))` 的并）
  -- 去掉一个指标只能让并变小 ⟹ `E ↑Sw ⊆ E ↑𝒮_φ`。
  -- 加这两条的**理由**：洞 2 的相邻性 `hadj` 是在 `E ↑𝒮_φ` 上给的，而洞 4/5/6 要的
  -- 是窗口 `Sw` 上的版本；`hEsub` 就是那座桥，缺了它 `hvlmin` 无从谈起。
  have hadjSw : ∀ n ∈ Nivat.LE2.E (↑Sw : Set (ℤ × ℤ)),
      ¬ (Nivat.LE2.dot n vl < 0 ∧ 0 < Nivat.LE2.dot n u') := fun n hn => hadj n (hEsub hn)
  -- **`hvlmin`：洞 4 / 洞 5 / 洞 6 的唯一共同残余**（2026-09-20）。
  -- 原文 `:766`：`ℓ₁,…,ℓ_{2m}` 是 `𝒮_φ` 的边方向，**按循环序**排列（「与 `ℓ_{i+1}` 平行的边
  -- 是与 `ℓ_i` 平行的边的后继」），而锥方向取的是 `ℓ` 的**前驱** `ℓ_{ι−1}`。相邻＝
  -- `vl` 与 `u'` 张成的开锥内没有 `𝒮_φ` 的边方向；边方向都避开一个开锥的凸多边形，
  -- 整体装得进该锥的一个平移，锚点正是 `hstrict` 选出的那个顶点。
  -- **消费者**：紧接着的洞 5（本文件，已接）、`CornerNeg.corner_le_of_strict_of_vlmin`
  -- （洞 4）、洞 6 的 `halfStrip` 位置条件。
  -- **生产者**：`VlMinAdj.vlmin_of_adjacent`（`VlMinAdj.lean`，集成者之手，2026-09-20 落地），
  -- 前提是 `hunimod`/`hperp`/`hnu` + `ha₀` + `hstrict` + `hadjSw`，**不要 `hSwconv`
  -- 也不要 `PosArea`**（`m = 2` 时 `𝒮_{φ_ι}` 是线段，正面积为假；共线分支单独证）。
  -- 🟢 **`hvlmin` 已关闭**：内核实测 `[propext, Classical.choice, Quot.sound]`。
  have hvlmin : ∀ z ∈ Sw,
      0 ≤ Nivat.LE2.dot (expNormal u' vl) (z - a₀) :=
    Nivat.VlMinAdj.vlmin_of_adjacent hunimod hperp hnu ha₀ hstrict hadjSw
  -- 🔴 **洞 4（`𝒮_φ` 的角点 `a`，挂在 `u'` 上）已删除**（2026-09-20，用户裁决
  -- 「按原文拆成两阶段」）。它上一版写的是
  --     `obtain ⟨a, ha, hcorner⟩ : ∃ a ∈ d.Sphi, ∀ b ∈ d.Sphi,`
  --     `  0 ≤ dot (expNormal u' vl) (b - a) ∧ 0 ≤ uCoord u' vl a b := sorry`
  -- 并把 `hcorner` 与同一段落里的 `hadj`（洞 2 产出）**绑在同一个 `(vl, u')` 上**。
  -- `CornerAdjClash.det_eq_zero_of_adj_of_corner`（`CornerAdjClash.lean:167`，内核事实、
  -- 公理干净）证明这样绑迫使 `𝒮_φ` 所有 `vl`-坐标为负的边法向两两平行，即 `m ≤ 2`；
  -- 而 `hcorner` 对剪切参数 `K` 上闭、`hmono` 下闭，两者只交于 `K = 0`，剪切救不了。
  -- 所以这不是「角点难证」，是**这个角点根本不在这一段的坐标框里**——
  -- 它属于 `:806-856`（Figure 11(B)）的第二阶段，方向对是 `(ℓ' = ℓ_I, v⃗_{ℓ_{I−1}})`，
  -- 而 `:814` 明写 `I` 一般 `≠ ι`。替代物是下面的 `exists_cutResidualR_of_claim46`
  -- （2026-09-21 起；旧名 `exists_stage2_frame_of_claim46` 已退役，`OPEN.md #21`），
  -- 它在**自己的框**里同时产出 `hbase₂` 与 `hcorner`（硬规矩 7：不发明量词，换回原文的框）。
  -- 洞 5：锥步。窗口平移后仍在切割线下方时，落回锥内。目标是
  -- `SweepLines.lean:289` 的 `hcone_coneStep_of_window`（已写陈述，未证）。
  -- ⚠ Lsweep 本轮实测：写在 `S` 上时**有反例**（`z` 的 `vl`-坐标可任意负，平移出锥）。
  -- 现在窗口是 `Sw`，仍需一条「窗口贴着锥的角」的前提；见洞 4 的 `hcorner`。
  -- 🟢 **洞 5 已关闭**（2026-09-20）：`Nivat.ConeStepWin.hcone_coneStep_of_window`
  -- （`ConeStepWin.lean:48`，内核实测 `[propext, Classical.choice, Quot.sound]`）。
  -- 两个坐标的分工：`vl`-坐标由 `hvlmin` 管，`u'`-坐标**免费**——`dot nℓ u' = -1`
  -- 使 `uCoord u' vl 0 x = - dot nℓ x`（`EnvFit.uCoord_eq_neg_dot_of_basis`），
  -- 于是「深度够」就是 `hcz` 配 `hzb`。上一版注释猜的「还需一条贴角前提」只对了一半：
  -- 贴角前提确实要，但只要在 `vl` 一侧。
  have hcone : ∀ w ∈ Nivat.ConeRegion.coneRegion B vl u',
      Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ Sw.erase a₀, Nivat.LE2.dot nℓ (z + (w - a₀)) < cz →
        z + (w - a₀) ∈ Nivat.ConeRegion.coneRegion B vl u' := by
    intro w hw hwb z hz hzb
    exact Nivat.ConeStepWin.hcone_coneStep_of_window hunimod hperp hnu hcz hvlmin hw hwb hz hzb
  -- 洞 6：半带步。窗口平移后越过切割线时，落进 `H_B(ℓ)`。
  -- 🔴 **2026-09-21 订正**：上一版这里写「已知唯一缺口是 μ 子句，且 `henv` 是唯一还没被
  -- 用上的前提」——**两句都不对**。μ 子句是 `hstrip_iff_fit_window` 那个编码的产物，
  -- 原文 `:786-804` 里没有对应物；`henv` 的内容全部落在下面的 `hplaceB` 里，不是「还没用上」。
  -- 🔴 **2026-09-21 二次订正：上一版推荐的 `hplaceB` 归约作废，`hplaceB` 在链上不可满足。**
  -- `Nivat.StripDescend.stripStep_of_place_of_down`（`StripDescend.lean:104`）本身是**真定理**
  -- 且无 `sorry`，但它的前提
  --   `hplaceB : ∀ b ∈ B, ∀ z ∈ Sw, cz ≤ dot nℓ (b + (z - a₀)) → b + (z - a₀) ∈ halfStrip B vl`
  -- 为假。算术：`dot nℓ vl = 0` ⟹ `halfStrip B vl = B + ℕvl` 的**层集合等于 `B` 的层集合**，
  -- 上界是 `B` 的最高层 `czTop`。取 `b` 为 `B` 的 `nℓ`-最高点、`z ∈ Sw` 比 `a₀` 高 `δ > 0`，
  -- 则 `b + (z − a₀)` 的层是 `czTop + δ > czTop`，**不可能**落在 `halfStrip` 里。
  -- 那条归约先把点抬到 `b + (z − a₀)` 再沿 `u'` 降 `t` 步，**抬那一下就出界**。
  -- 这是「比原文强 = 债」（硬规矩 7）落在**前提**位置上的实例：真定理 + 空前提 = 零进度。
  -- 死因可机械复述：该归约**丢掉了 `dot nℓ w < cz`**，而那条正是把层压回 `B` 值域的唯一耦合。
  --
  -- 🟢 **保留耦合之后的正确分解**（`w = b + s•vl + t•u'`，`s t : ℕ`）：
  --   `dot nℓ w = dot nℓ b − t < cz` ⟹ `t > dot nℓ b − cz ≥ 0`（用 `hcz`）；
  --   记 `δ := dot nℓ (z − a₀) ≥ 0`（`:798` 的锚点 `a₀` 落在 `A₁ = 𝓡_{ι−1} ∩ ℓ_B^{(−)}`，
  --   即窗口最低点，其余点都在 `H_B(ℓ)` 内，故 `δ ≥ 0`），则
  --   `L := dot nℓ (z + (w − a₀)) = dot nℓ w + δ < cz + δ`。
  -- 🟢 **2026-09-21 三次订正：上一版的 (O1)/(O2) 两支分解也作废，已被一条更短的路线取代。**
  -- 作废的理由是读法错误，不是算术错误：(O2) 假定要比较窗口与 `B` 的**左下轮廓函数**
  -- （`leftprof L := min {dot m b : b ∈ B, dot nℓ b = L}`），并把 `L > dot nℓ b` 那一支
  -- 标成「Claim 4.6 原文没写的那一步」。但原文 `:794-796` 的归纳是**向下**跑的——
  --   `A₁ := 𝓡_{ι−1} ∩ l₁`，`l₁ := ℓ_B^{(−)}`；`A₂ := 𝓡_{ι−1} ∩ l₂`，`l₂ := l₁^{(−)}`；
  --   "Proceeding this way, we get by induction"
  -- ——所以窗口 `Ŝ_{φ_ι}` 是**以它的唯一最低点坐在 `A₁` 上**摆进去的，其余点全在 `H_B(ℓ)` 内。
  -- 把这句话直译过来，要的不是两条轮廓函数的比较，而是**一个锚定的平移**：
  --   取 `c` 使 `Sw + c ⊆ B` 且 `a₀ + c` 恰是 `B` 底层 `cz` 的最左点 `g`。
  -- 有了它，`z + c ∈ B` 位于层 `cz + δ`，而目标层 `L ≤ cz + δ − 1` 在其**下方**，
  -- 于是沿 `u'` 逐行下降（`StripDescend.exists_row_left_of_stepdown`）即可；
  -- `m`-坐标的比较由「`g` 是最左点」白给。两行算术，不需要轮廓函数、不需要斜率序列。
  --
  -- 🟢 **归约已全部落地，`StripDescend.lean` 内核实测公理干净**（链自顶向下）：
  --   `hstrip` ⟸ `StripDescend.hstrip_of_suppVal`
  --           ⟸ `hstrip_of_fit` ∘ `fit_of_suppVal_le`
  --           ⟸ (`hstrip_of_profile`, `hdesc_of_row`, `hprof_of_fit`)
  -- 需要喂的东西：`hczlow`（本文件 `hcz` 白给）、`hrow`（逐行下降，`RowHit` 一支）、
  -- `hglev`/`hgleft`（`StripDescend.exists_bottom_left`，纯有限性，已证），
  -- 以及**唯一剩下的几何义务**
  --   `hsupp : ∀ n ∈ E B, suppVal ↑Sw n + dot n (g − a₀) ≤ suppVal B n`。
  -- ⚠ **读法（硬规矩 3）：几何被搬走了，没有被消掉。** 上面这条链本身是纯算术；
  -- Claim 4.6 的全部几何内容现在集中在 `hsupp` 一条里。
  --
  -- `hsupp` 的内容 ＝ 「enveloped 的 `B` 含 `Sw` 的一个平移」的支撑函数形态
  -- （Definition 3.2，`:402`；`Enveloped.E_eq`，`LatticeEdges.lean:1657` 给两边法向集合相同）。
  -- 机制：同法向集合 ＋ `B` 每条边不短 ⟹ `B = Sw + K`（Minkowski，`K` 是边长差的 zonotope），
  -- 取 `c := g_B − g_Sw` 两个词典序角点之差即可。**这一步原文没写。**
  -- ⚠ 该论证**必须带 `IsLatticeConvexRegion ↑Sphi`**——不带就被
  -- `ConeWindowBox.not_width_le_of_enveloped`（`:881`）用 `stretch`/`sq1` 当场证伪。
  -- 链上生产者免费：`ChainAsm.isLatticeConvexRegion_coe`（`ChainAssemble.lean:347`）。
  -- ⚠ **不要写成 `chi` 值域的绝对包含**：`enveloped_shift_right`（`LatticeEdges.lean:1679`）
  -- 是 `@[simp]`，envelopedness 平移不变而绝对包含不是，那种陈述加凸性也救不回来。
  --
  -- ⚠ 三条已排除的省事写法，不要重派：
  --   (a) 宽度形态 / 平移不变形态：会要求单个点 `g` 对**所有** `n ∈ E B` 同时满足
  --       `dot n g = −suppVal B (−n)`，二维不可能。
  --   (b) 「先随便取一个平移，再滑到角上」：滑动要求 `dot n (g − q) ≤ 0` 对所有 `n ∈ E B`，
  --       而 `E B` 正张成 ℝ²，逼出 `g = q`，等于没省。
  --   (c) 弱化 `hleft`（不要求落在角点）：`hprof_of_fit` 对**所有**层 `cz` 上的 `b₀` 取全称，
  --       最左点是被逼出来的，不是我们挑的。
  -- ⚠ **不要再对 `hplaceB` 派工**（它为假），也不要对「整条 `hstrip`」派工——派 `hsupp`。
  --
  -- ═══ 2026-09-21：`hstrip` 已接线，`sorry` 缩到三条 `𝒮_φ`-侧义务 ═══
  -- 免费的三条（都不占洞）：
  --   `E ↑𝒮_φ = E B`（`Nivat.LE2.Enveloped.E_eq`，`LatticeEdges.lean:1657`）把洞 2 的
  --     `hadj` 原样搬到 `B` 上；
  --   `IsLatticeConvexRegion B` 就是 `henv.1.latticeConvex`
  --     （`WeaklyEnveloped.latticeConvex`，`LatticeEdges.lean:634`）；
  --   `±nℓ ∈ E ↑𝒮_φ` 由洞 1 的 `hdoth` 白给
  --     （`DecompData.mem_E_Sphi_of_dot_eq_zero` / `neg_mem_…`，`FaceDistinct.lean:146/159`）。
  have hSphiFin : (↑d.toDecompData.Sphi : Set (ℤ × ℤ)).Finite :=
    d.toDecompData.Sphi.finite_toSet
  have hESphiFin : (Nivat.LE2.E (↑d.toDecompData.Sphi : Set (ℤ × ℤ))).Finite :=
    Nivat.LE2.finite_E_of_finite hSphiFin
  have hEeq : Nivat.LE2.E B = Nivat.LE2.E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) :=
    Nivat.LE2.Enveloped.E_eq hESphiFin henv
  have hadjB : ∀ n ∈ Nivat.LE2.E B,
      ¬ (Nivat.LE2.dot n vl < 0 ∧ 0 < Nivat.LE2.dot n u') := by
    rw [hEeq]; exact hadj
  have hlcB : Nivat.IsLatticeConvexRegion B := henv.1.latticeConvex
  have hnℓ_mem : nℓ ∈ Nivat.LE2.E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) :=
    d.toDecompData.mem_E_Sphi_of_dot_eq_zero hprim i hdoth
  have hnℓ_neg_mem : -nℓ ∈ Nivat.LE2.E (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) :=
    d.toDecompData.neg_mem_E_Sphi_of_dot_eq_zero hprim i hdoth
  -- 🟢 **2026-09-21 复核：原以为的三条残余义务里，两条是免费的。**
  -- (1) `PosArea ↑𝒮_φ` ＝ `AhatMono.posArea_Sphi`（`AhatMono.lean:3175`，无条件，
  --     只用 `d.hm : 2 ≤ d.m` 与 `h_dir`），经 `posArea_of_enveloped`（`:3020`）传到 `B`。
  -- (2)(3) `±nℓ` 两个面上各有两个不同格点 ＝ `Nivat.LE2.mem_E_iff`
  --     （`LatticeEdges.lean:219`，`n ∈ E R ↔ Prim n ∧ (face R n).Nontrivial`）用在
  --     `hnℓ_mem` / `hnℓ_neg_mem` 上，再经 `SweepCrit.exists_two_in_face_of_enveloped`
  --     （Definition 3.2 的边长不等式）传到 `B`。
  --     ⚠ `hrow` **不带这两条就是假的**：反例见
  --     `SweepCrit.exists_level_down_of_unitCovered` 的 docstring
  --     （`B = Conv{(0,0),(3,1),(1,3)} ∩ ℤ²`，`nℓ = (1,1)`，`PosArea` 成立，层 1 为空）。
  have hareaB : Nivat.LE2.PosArea B :=
    Nivat.AhatMono.posArea_of_enveloped hSphiFin
      (Nivat.AhatMono.posArea_Sphi d.toDecompData) henv
  have htopB : ∃ a b, a ∈ Nivat.LE2.face B nℓ ∧ b ∈ Nivat.LE2.face B nℓ ∧ a ≠ b := by
    obtain ⟨a, ha, b, hb, hab⟩ := (Nivat.LE2.mem_E_iff.mp hnℓ_mem).2
    exact Nivat.SweepCrit.exists_two_in_face_of_enveloped hESphiFin henv hnℓ_mem
      ⟨a, b, ha, hb, hab⟩
  have hbotB : ∃ a b, a ∈ Nivat.LE2.face B (-nℓ) ∧ b ∈ Nivat.LE2.face B (-nℓ) ∧ a ≠ b := by
    obtain ⟨a, ha, b, hb, hab⟩ := (Nivat.LE2.mem_E_iff.mp hnℓ_neg_mem).2
    exact Nivat.SweepCrit.exists_two_in_face_of_enveloped hESphiFin henv hnℓ_neg_mem
      ⟨a, b, ha, hb, hab⟩
  -- 🔴 **洞 6 的残余义务现在只剩这一条**，就是 Claim 4.6 的全部几何内容：
  -- 「`E(𝒮_φ)`-enveloped 的 `B` 含窗口 `Sw` 的一个平移」的支撑函数形态，
  -- 平移锚在 `B` 的底层最左点 `g` 上。**原文没写这一步**，见上方长注释。
  --
  -- 🟢 **2026-09-21：窗口那一侧已整个算掉，`Sw` 不再出现在残余义务里。**
  -- `:792` 的 `φ_ι := ∏_{j≠ι₀}(X^{h_j}−1)` 说明 `Conv Sw` 就是**去掉生成元 `i`** 的
  -- zonotope（`hSwzono`，由 `exists_window_strict_at_prime` 导出）。于是
  --   * `a₀ = zonoArgmin (univ.erase i) h nℓ`（`ColleReg.eq_zonoArgmin_of_strict`）——
  --     `hstrict`（`:794` 的「最低那条线上只有一个点」）把严格极小点钉死；
  --   * `suppVal ↑Sw n − ⟪n, a₀⟫ = ∑_{j≠i} max 0 ⟪n, orientUp (h j) nℓ⟫`
  --     （`ColleReg.relSuppVal_zonoF` ＋ `suppVal_congr_of_Conv_eq`）——纯代数。
  -- 剩下的 `hsuppZ` 只谈 `B`、`g` 与生成元，**一个 zonotope 对象都没有**：
  -- 它就是 Definition 3.2（`:402`）的「`B` 的每条边不短于 `𝒮_φ` 的对应边」在支撑函数上
  -- 的读法 ——「从 `B` 的底左角 `g` 出发，沿 `n`-正向的那些生成元各走一步，仍在 `B` 里」。
  have hSwne : Sw.Nonempty := ⟨a₀, ha₀⟩
  have hzne : (Nivat.LE2.zonoF (Finset.univ.erase i) d.toDecompData.h).Nonempty :=
    ⟨Nivat.ColleReg.zonoArgmin (Finset.univ.erase i) d.toDecompData.h nℓ,
      Nivat.ColleReg.zonoArgmin_mem _ _ _⟩
  have ha₀eq : a₀ = Nivat.ColleReg.zonoArgmin (Finset.univ.erase i) d.toDecompData.h nℓ :=
    Nivat.ColleReg.eq_zonoArgmin_of_strict hSwconv hSwzono ha₀ hstrict
  have hrel : ∀ n : ℤ × ℤ,
      Nivat.LE2.suppVal (↑Sw : Set (ℤ × ℤ)) n - Nivat.LE2.dot n a₀ =
        ∑ j ∈ Finset.univ.erase i,
          max 0 (Nivat.LE2.dot n
            (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ)) := by
    intro n
    rw [Nivat.ColleReg.suppVal_congr_of_Conv_eq n hSwne hzne hSwzono, ha₀eq]
    exact Nivat.ColleReg.relSuppVal_zonoF _ _ nℓ n
  -- 🟢 **2026-09-21 第二步：再把 `erase i` 抬成整个 `𝒮_φ`。**
  -- `:792` 的窗口是 `𝒮_φ` **去掉一个生成元**，每一项 `max 0 ⟪n,·⟫` 非负，所以子集和
  -- 不超过全集和（`ColleReg.relSuppVal_zonoF_mono`）。于是残余义务里连 `i` 都消失了，
  -- 剩下的 `hsuppFull` 是**关于 `𝒮_φ` 与 `B` 的一句话**，正是 Definition 3.2
  -- （`b3_colle2.txt:402`）声称的几何内容：`E(𝒮_φ)`-enveloped 的 `B` 含有 `𝒮_φ` 的一个
  -- 整格平移，且平移可以把 `𝒮_φ` 的字典序最低角点送到 `B` 的字典序最低角点 `g`。
  -- 等价签名 `Nivat.SweepBase.exists_shift_subset_of_envOf`（`SweepBase.lean:404-430`
  -- 记着它被撤下的经过）——**欠的是格凸多边形的 Minkowski 分解，不是接线。**
  -- 🔴 **2026-09-22 撤回 `hsuppFull`（整个 `𝒮_φ` 版）：它为假。** lane hsupp-prove 的数值实例
  -- （`m = 3`、`h = ((±2,0),(1,2),(-1,2))`、`nℓ = (0,1)`、`vl = (1,0)`、`B = 𝒮_φ` 自身）：
  -- `h i ∥ vl` 时 `⟪nℓ, h i⟫ = 0`，`orientUp` 不翻转，`zonoArgmin univ h nℓ` 落在底边的
  -- **`h i` 那一端**，而 `g` 按 `hgleft` 固定是**左端**；`h i = (-2,0)` 取向下 `hsuppFull`
  -- 在 3 条边法向里的 2 条上为假，`hsuppZ`（去掉生成元 `i`）在两种取向下都真。
  -- 失败的是我们把 `erase i` 抬成 `univ` 那一步（`:2884-2886`），不是原文；`:792` 的窗口
  -- 本来就是 `𝒮_{φ_ι}`（去掉一个生成元）。残余义务改为直接证 `hsuppZ`。
  -- 2026-09-22（lane-chain 证伪，集成者改）：原陈述漏了 `g ∈ B`——`g` 沿 `vl` 推到 `B` 之外仍满足
  -- 两条前提，而 RHS 随 `dot n g` 变化，`0 ≤ −2` 出现在 `LEAF-HSUPP.md` §1 的实例上
  -- （`tmp/wip/hsuppZ_target_FALSIFIED.md`）。调用点的 `g` 来自 `exists_bottom_left`，本来就在 `B` 里。
  have hencard : ∀ n ∈ Nivat.LE2.E B,
      (Nivat.LE2.face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) n).encard ≤
        (Nivat.LE2.face B n).encard :=
    fun n hn => Nivat.LE2.Enveloped.face_encard_le hESphiFin henv (hEeq ▸ hn)
  have hsuppZ : ∀ g : ℤ × ℤ, g ∈ B → Nivat.LE2.dot nℓ g = cz →
      (∀ b ∈ B, Nivat.LE2.dot nℓ b = cz →
        Nivat.LE2.dot (expNormal u' vl) g ≤ Nivat.LE2.dot (expNormal u' vl) b) →
      ∀ n ∈ Nivat.LE2.E B,
        (∑ j ∈ Finset.univ.erase i,
            max 0 (Nivat.LE2.dot n
              (Nivat.ColleReg.orientUp (d.toDecompData.h j) nℓ))) ≤
          Nivat.LE2.suppVal B n - Nivat.LE2.dot n g :=
    fun g hgB hgcz hgmin n hn =>
      Nivat.HsuppAssemble.hsuppZ_target_proof hBfin hBne hlcB hprim hperp hdoth hunimod hnu
        hEeq hnℓ_neg_mem hencard hcz g hgB hgcz hgmin n hn
  have hsupp : ∀ g : ℤ × ℤ, g ∈ B → Nivat.LE2.dot nℓ g = cz →
      (∀ b ∈ B, Nivat.LE2.dot nℓ b = cz →
        Nivat.LE2.dot (expNormal u' vl) g ≤ Nivat.LE2.dot (expNormal u' vl) b) →
      ∀ n ∈ Nivat.LE2.E B,
        Nivat.LE2.suppVal (↑Sw : Set (ℤ × ℤ)) n + Nivat.LE2.dot n (g - a₀) ≤
          Nivat.LE2.suppVal B n := by
    intro g hgB hglev hgleft n hn
    have h1 := hrel n
    have h2 := hsuppZ g hgB hglev hgleft n hn
    have h3 : Nivat.LE2.dot n (g - a₀) = Nivat.LE2.dot n g - Nivat.LE2.dot n a₀ :=
      Nivat.LE2.dot_sub n g a₀
    omega
  have hstrip : ∀ w ∈ Nivat.ConeRegion.coneRegion B vl u',
      Nivat.LE2.dot nℓ w < cz →
      ∀ z ∈ Sw.erase a₀, cz ≤ Nivat.LE2.dot nℓ (z + (w - a₀)) →
        z + (w - a₀) ∈ Nivat.LE2.halfStrip B vl := by
    have htwoPos : ∃ a b, a ∈ Nivat.LE2.face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) nℓ ∧
        b ∈ Nivat.LE2.face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) nℓ ∧ a ≠ b := by
      obtain ⟨a, ha, b, hb, hab⟩ := (Nivat.LE2.mem_E_iff.mp hnℓ_mem).2
      exact ⟨a, b, ha, hb, hab⟩
    have htwoNeg : ∃ a b, a ∈ Nivat.LE2.face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) (-nℓ) ∧
        b ∈ Nivat.LE2.face (↑d.toDecompData.Sphi : Set (ℤ × ℤ)) (-nℓ) ∧ a ≠ b := by
      obtain ⟨a, ha, b, hb, hab⟩ := (Nivat.LE2.mem_E_iff.mp hnℓ_neg_mem).2
      exact ⟨a, b, ha, hb, hab⟩
    have hrow : ∀ b ∈ B, cz ≤ Nivat.LE2.dot nℓ b - 1 →
        ∃ c ∈ B, Nivat.LE2.dot nℓ c = Nivat.LE2.dot nℓ b - 1 :=
      Nivat.SweepCrit.hrow_of_enveloped_segments hESphiFin hBfin hBne hareaB hlcB henv
        hprim.ne_zero hvl_prim hvl_prim.ne_zero hperp hnu hnℓ_mem hnℓ_neg_mem
        htwoPos htwoNeg hczmem
    obtain ⟨b₀, hb₀, hb₀lev⟩ := hczmem
    obtain ⟨g, hgB, hglev, hgleft⟩ :=
      Nivat.StripDescend.exists_bottom_left (B := B) (nℓ := nℓ) (cz := cz)
        (m := expNormal u' vl) hBfin hb₀ hb₀lev
    exact Nivat.StripDescend.hstrip_of_suppVal (m := expNormal u' vl) (g := g)
      hBfin hBne hareaB hlcB hunimod hadjB hperp hnu
      (Nivat.ColleReg.dot_expNormal_vl hunimod) Nivat.ColleReg.dot_expNormal_u'
      hcz hrow ⟨a₀, ha₀⟩ hglev hgleft (hsupp g hgB hglev hgleft)
  -- ═══ 两阶段收尾（2026-09-20，用户裁决「按原文拆成两阶段」）═══
  -- 阶段一 = Claim 4.6（`:780-804`），结论是 `𝓡_{ι−1}` 上的周期性，**不提角点**。
  obtain ⟨c, hc, hbase₁⟩ :=
    claim46_of_case1 (e := e) d hSwgen ha₀ hconv henv hBfin hBne hunimod hvl_prim hu
      hp_mem hp_ne hdet_vl hperp hnu hstrict hprim i hdoth hcz hczmem hadj hcone hstrip
  -- 阶段二 = `:806-856`。🔴 **2026-09-21 换框**（`OPEN.md #21`）：不再经
  -- `exists_stage2_frame_of_claim46` → `wedgeResidualR_of_stage2_frame`（`chainFull` 象限，
  -- 层沿 `-vl` 暴露），改为原文自己的 `𝓡^n_I`（`:818`，层沿 `v⃗_{ℓ_{I−1}}`）。
  exact exists_cutResidualR_of_claim46 hξ d hgen henv hBfin hBne hunimod hvl_prim hc hperp
    hdetpos hnu hbase₁ hprim i hdoth hadj

/-- **L1's residual after `L1Assemble`'s mechanical half** (`L1Assemble.lean:819`, `section DerivedCut`).

`exists_L1Data` below asks for all fifteen fields of `L1Data`.  `L1Assemble.lean` discharges
seven of them from the two leaf binders `hdef` and `hSgen` plus the choice `S₁ := S.image (· + v)`
— the cut normal, the two face levels, conjunct 1 (by `isGeneratingSet_image`), conjunct 4, and
conjunct 7 — leaving `MaxBResidual`'s **six** fields together with the four proof fields of
`Nivat.L1Region.RegionFamily`.  This declaration is that residual and nothing else.

**Why this is stated in terms of a structure and not its fields.**  Deliberate: the statement
names the structure, so a change to the structure's field list does not change this statement
and does not break the assembly below.  Splitting against a *name* rather than against a *field
list* is what makes the split survive the work it enables.

**2026-09-19 — the residual is now `MaxBResidual`, six fields, not `DerivedResidual`'s eight.**
The two are not a re-encoding: `Nivat.ColleReg.L1Data.maxBResidual_of_derived`
(`L1Assemble.lean:1076`, kernel-clean, measured) proves `DerivedResidual → MaxBResidual` under
`S₁.Nonempty` and `LatticeConvex S₁`, so **this obligation is strictly weaker than the one it
replaces**.  What changed is the choice of baseline: `B := maxB Q u' pw`
(`L1Assemble.lean:979`), the largest set conjunct 8 admits, under which conjunct 8 is
`Finset.mem_filter` and conjunct 16 is as weak as it can be.  `lt` and `card` are gone — they
existed only to put the bottom-face anchor into a singleton `B` — and `base0` becomes an
existential over `maxB` rather than a universal over the bottom face.

⚠ `sorry TOTAL` is unchanged by this rewiring, and so is `axiom_closure`.  Per `CLAUDE.md` hard
rule 1 that means **zero progress**; what it buys is that the remaining obligation is smaller
and that `maxB_wide` (`L1Assemble.lean:1279`) — which produces
`min |top u-face| |bottom u-face| − 1` consecutive `u`-translates inside `maxB` — now speaks
about the baseline this `sorry` actually has to produce.

⚠ **Split, not progress**, exactly as for `exists_case2_window`: `sorry TOTAL` is unchanged and
`axiom_closure` is unchanged.  What it buys is that `L1Assemble.lean`'s 1013 verified lines are
now **on the chain**.  Before this, `grep -rln "Colle.L1Assemble" Nivat/` returned `All.lean`
and nothing else: seventeen kernel-clean declarations with no consumer, in precisely the shape
`CLAUDE.md` records for `L1Data` itself — *"把 16 合取拆成具名字段的那一步，从来没接到它拆的那条
`sorry` 上"*.  Wiring is an independent landing action; it does not happen because more lemmas
accumulate. -/
theorem exists_L1MaxBResidual
    (hξ : IsMinimalCounterexample ξ) (d : DecompDataZ ξ)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    -- **The second orientation, threaded 2026-09-19.**  `hℓ_nel` alone is *one* orientation;
    -- Collé's Lemma 4.1 stands on `-ℓ, ℓ ∈ nexpd(η)` (`b3_colle2.txt:607`), and it is the pair
    -- that Lemma 2.3 turns into "`𝒮` has an edge parallel to `ℓ` **and another one parallel to
    -- `-ℓ`**" (`:627`).  Both edges are what give the parallelogram of `maxB_wide`
    -- (`L1Assemble.lean:1310`) positive width; with one orientation its width is `0` and every
    -- `maxB`-based field of `MaxBResidual` is vacuous.  The bridge to the edge is
    -- `ONEDRational.toReal_mem_ONED_of_isOneSidedNonexpansive` (`:169`) followed by
    -- `R2.two_le_face_card_of_mem_ONED` (`R2Orientation.lean:171`) — note it consumes
    -- `IsOneSidedNonexpansive`, **not** `NonExpansiveLine`, which is why `hℓ_nel` could never
    -- reach it.  Free at the call site: `ColleRegion.lean:356`, before the case split.
    (hℓ_pos : Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hxper : xper ∈ orbitClosure ξ) (hgen : Nivat.Colle.GeneratesAt ξ S gen)
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (hp_mem : p ∈ Per xper) (hp_ne : p ≠ 0) (hvl_ne : vl ≠ 0) (hvl_prim : Primitive vl)
    (hdet_vl : det p vl = 0) (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0)
    (hdef : ∀ (n : ℝ × ℝ) (cmax cmin : ℝ),
      (∀ z ∈ S, inner2 n z ≤ cmax) → (Nivat.R2.face S n cmax).Nonempty →
      (∀ z ∈ S, cmin ≤ inner2 n z) → (Nivat.R2.face S n cmin).Nonempty →
        P ξ S - P ξ (S.filter fun z => inner2 n z < cmax) ≤
          (Nivat.R2.face S n cmax).card - 1 ∧
        P ξ S - P ξ (S.filter fun z => cmin < inner2 n z) ≤
          (Nivat.R2.face S n cmin).card - 1)
    (hcase1 : Case1 ξ xper d.Sphi vl) :
    ∃ (e u u' v : ℤ × ℤ) (c τ : ℤ) (ε : Bool) (S₁ : Finset (ℤ × ℤ))
      (F : Nivat.L1Region.RegionFamily (T e ξ) u u' c),
      S₁ = S.image (· + v) ∧
      Nivat.ColleReg.L1Data.MaxBResidual (ξ := ξ) ε u u' c τ S₁ F :=
  (exists_cutResidualR hξ d hℓ_nel hℓ_pos hℓ_neg hxper hgen hSgen hp_mem hp_ne hvl_ne
      hvl_prim hdet_vl hdet_ℓ hdef hcase1).elim fun r =>
    L1Claim.exists_L1MaxBResidual_of_cutResidualR hℓ_nel hℓ_neg hSgen hvl_prim hdet_ℓ r

/-- **L1's obligation, relocated onto `L1Data`** (`L1Data.lean:71`).

This carries exactly the same mathematical content as the `sorry` that used to sit on
`case1_claim46_and_selection` below — `L1Data.toConclusion` (`L1Data.lean:148`) turns one of
these into that theorem's conclusion with no side conditions, so the two are interderivable
and the `sorry` count is unchanged at four.

**What it buys is that `L1Data` is now on the dependency chain of the main theorem.**  Measured
2026-09-18 (`tmp/onchain_scan.py`, transitive `import` closure from `Nivat.Section8.Main`):
before this declaration, 58 of the tree's 158 modules were unreachable from `nivat_conjecture`,
and `L1Data` was one of them — nothing imported the structure built to split this very `sorry`.
That is why several thousand lines of L1 lemmas had moved `sorry TOTAL` by zero: they were all
downstream of `L1Data`, which was itself downstream of nothing.

With the obligation stated here, the remaining work is "construct an `L1Data`", i.e. discharge
its **fifteen** named fields (`L1Data.lean:96-136`) one at a time, each of which is a statement
the kernel can check on its own.  Contrast the old form, which was a single sixteen-conjunct
existential that could not be split across workers.

⚠ This is a **relocation, not progress**: no field is discharged here, and `axiom_closure` is
untouched.  Per `CLAUDE.md` hard rule 4 ("拆而后落"), the mechanical split goes in before the
work is dispatched, not after — and per the same rule, wiring the split onto the chain is a
separate landing action that does not happen automatically as more lemmas accumulate.

**2026-09-19 — the conclusion is now `L1DataMax`, not `L1Data`.**  `L1DataMax`
(`L1Assemble.lean:1050`) is `L1Data` plus one field, `hBmax`, naming the baseline `B` as
`maxB (derivedQ ε u' S₁) u'` at width `(topFace ε u' S₁).card - 1`.  `case1_seed` needs it and
nothing else does.

It was put on an *extension* rather than on `L1Data` itself for a reason worth keeping: other
producers of `L1Data` build a singleton or translated `B` that is **not** `maxB`, and a field on
the base structure would break every one of them for no gain, since only `ofMaxB` is on the
chain.  `L1Data.lean` is untouched.  `MaxBResidual` gains no field either — `ofMaxB` already
constructs `B` and `pw` in exactly that form, so `hBmax := ⟨ε, rfl, rfl⟩`.  **This theorem's
binder list is unchanged and leaf L1's obligation is unchanged**; only the name of the bundle
it returns moved. -/
theorem exists_L1Data
    (hξ : IsMinimalCounterexample ξ) (d : DecompDataZ ξ)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    -- Passed straight through to `exists_L1MaxBResidual` (`:843`); see the note there.
    (hℓ_pos : Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hxper : xper ∈ orbitClosure ξ) (hgen : Nivat.Colle.GeneratesAt ξ S gen)
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (hp_mem : p ∈ Per xper) (hp_ne : p ≠ 0) (hvl_ne : vl ≠ 0) (hvl_prim : Primitive vl)
    (hdet_vl : det p vl = 0) (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0)
    (hdef : ∀ (n : ℝ × ℝ) (cmax cmin : ℝ),
      (∀ z ∈ S, inner2 n z ≤ cmax) → (Nivat.R2.face S n cmax).Nonempty →
      (∀ z ∈ S, cmin ≤ inner2 n z) → (Nivat.R2.face S n cmin).Nonempty →
        P ξ S - P ξ (S.filter fun z => inner2 n z < cmax) ≤
          (Nivat.R2.face S n cmax).card - 1 ∧
        P ξ S - P ξ (S.filter fun z => cmin < inner2 n z) ≤
          (Nivat.R2.face S n cmin).card - 1)
    (hcase1 : Case1 ξ xper d.Sphi vl) :
    Nonempty (Nivat.ColleReg.L1DataMax ξ S) := by
  obtain ⟨e, u, u', v, c, τ, ε, S₁, F, hS₁, H⟩ :=
    exists_L1MaxBResidual hξ d hℓ_nel hℓ_pos hℓ_neg hxper hgen hSgen hp_mem hp_ne hvl_ne
      hvl_prim hdet_vl hdet_ℓ hdef hcase1
  exact Nivat.ColleReg.L1DataMax.nonempty_of_maxB e u u' v c τ ε S₁ F hS₁ hdef
    hSgen H

/-- **L1 — Claim 4.6 plus the `I`/`N` selection** (`b3_colle2.txt:780-820`).

Produces `ξ' = T^u η` together with every piece of data Lemma 4.1 consumes: the directions
`u ∥ ℓ` and `u' = v_{ℓ'}`, the sub-window `Q ⊆ S`, the baseline `B`, the region `R = 𝓡^N_I`
and its period `c • u`.

It also exports the successor region `R' = 𝓡^{N+1}_I` and the three facts that carry the
**maximality of `N`** (`:816-820`): `R ⊂ R'`, `¬ PeriodOn ξ' R' (c • u)`, and the straddling
condition.  Claim 4.7 is false without them — its proof is exactly "otherwise the period
propagates to `𝓡^{N+1}_I`, contradicting maximality of `N`" (`:822-852`).

`pw` is Lemma 4.1's pattern-width parameter (Collé's `p`).  It is **not** the `p ∈ Per xper`
of `region_case1`, which is already bound as a section variable. -/
theorem case1_claim46_and_selection
    (hξ : IsMinimalCounterexample ξ) (d : DecompDataZ ξ)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    -- Passed straight through to `exists_L1Data` (`:912`); see the note at `:843`.
    (hℓ_pos : Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hxper : xper ∈ orbitClosure ξ) (hgen : Nivat.Colle.GeneratesAt ξ S gen)
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (hp_mem : p ∈ Per xper) (hp_ne : p ≠ 0) (hvl_ne : vl ≠ 0) (hvl_prim : Primitive vl)
    (hdet_vl : det p vl = 0) (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0)
    (hdef : ∀ (n : ℝ × ℝ) (cmax cmin : ℝ),
      (∀ z ∈ S, inner2 n z ≤ cmax) → (Nivat.R2.face S n cmax).Nonempty →
      (∀ z ∈ S, cmin ≤ inner2 n z) → (Nivat.R2.face S n cmin).Nonempty →
        P ξ S - P ξ (S.filter fun z => inner2 n z < cmax) ≤
          (Nivat.R2.face S n cmax).card - 1 ∧
        P ξ S - P ξ (S.filter fun z => cmin < inner2 n z) ≤
          (Nivat.R2.face S n cmin).card - 1)
    (hcase1 : Case1 ξ xper d.Sphi vl) :
    ∃ ξ' ∈ orbitClosure ξ, ∃ (u u' : ℤ × ℤ) (Q : Finset (ℤ × ℤ)) (τ : ℤ) (pw : ℕ)
      (B : Finset (ℤ × ℤ)) (R R' : Set (ℤ × ℤ)) (c : ℤ) (S₁ : Finset (ℤ × ℤ)),
      -- **`ξ'` is a translate of `ξ`.**  `b3_colle2.txt:778`: Case 1 opens *"suppose there
      -- exists `u ∈ ℤ²` such that `(T^u η)|H_B(ℓ) = x_per|H_B(ℓ)`"*, and `ξ' := T^u η`.  The
      -- translation vector is handed over by `hcase1` itself (`Case1`, `:326-328`), so this
      -- conjunct costs the proof of this leaf nothing.
      --
      -- ⚠ **The `u` bound just above is NOT that translation vector.**  The paper's `u` (the
      -- translation) and the Lean `u` (the direction of the period `h = c • u`, `:806`) are
      -- different objects that the paper writes with different letters; `u` was chosen here
      -- for the period direction, so the translation has no name in this signature and needs
      -- its own existential.  The docstring of `region_case1` below still says "`ξ' := T u ξ`"
      -- in the *paper's* letters — that is the paper's `u`, not this one.
      --
      -- Consumed by `region_case1` to discharge `¬ IsPeriodic ξ'` through
      -- `CosetPigeonhole.not_isPeriodic_T_of_not_isPeriodic` (`PeriodTransport.lean:24`).
      -- **`S₁` is the translated generating window** — Collé's `𝒯`, a translate of `𝒮`
      -- (`b3_colle2.txt:824`).  Exported as a *set* rather than as the translation vector `v`
      -- because `S` is a file-level `variable` (`:218`), so L2/L3 are already generic in the
      -- window and need no signature change to run on `S₁` instead of `S`; and because
      -- `region_case1`'s conclusion (`:1121-1128`) mentions no window at all, so the
      -- substitution is invisible to everything above this leaf.
      --
      -- Collé states Claim 4.7 for *every* qualifying translate; this exports *one*.  The gap
      -- is smaller than it reads: the family of translates *along* `ℓ'` is already internal to
      -- `SemiAmbiguousAlong`'s own `∀ t ≥ τ` over positions `t • u'` (`Lemma41.lean:542`), so
      -- what the existential fixes is only the *level* transverse to `ℓ'` — and the straddle
      -- pins that to the boundary of shell `N`.  See `blueprint/NOTE.md`.
      Nivat.Colle.IsGeneratingSet ξ S₁ ∧
      (∃ e : ℤ × ℤ, ξ' = T e ξ) ∧
      Q ⊆ S₁ ∧
      -- `Q = 𝒮 ∖ ℓ'_𝒮` (`b3_colle2.txt:822`, the hypothesis `𝒯 ∖ ℓ'_𝒯 ⊂ 𝓡^N_I` of Claim 4.7):
      -- what is discarded is exactly the edge of `S` *parallel to* `ℓ'`, i.e. to `u' = v_{ℓ'}`,
      -- hence `inner2 n u' = 0`.  Maximising face, per the sign convention certified at
      -- `R2Orientation.lean:92`.  Needed at `b3_colle2.txt:844` to seed the `u'`-ray with a
      -- `g ∈ 𝒯 ∩ ℓ'_𝒯`; `Q ⊆ S` alone does not supply it (`blueprint/NOTE.md`, entry
      -- "SemiAmbiguousAlong …").
      --
      -- `n ≠ 0` is **not** decoration.  `b3_colle2.txt:253` defines edge through a supporting
      -- line, and a line has a non-zero normal; without the clause `n := 0`, `cmax := 0`
      -- satisfies the other four conjuncts for every non-empty `S` (`inner2 0 u' = 0`,
      -- `inner2 0 z = 0 ≤ 0`, `face S 0 0 = S`) and yields `Q = S.filter (fun _ => (0:ℝ) < 0)
      -- = ∅`.  That branch is neither of Collé's two at `:840` — it is the degenerate
      -- "the edge is all of `S`" case, which he never enters because `ℓ'_𝒮` is an edge.
      (∃ (n : ℝ × ℝ) (cmax : ℝ),
        n ≠ 0 ∧
        inner2 n u' = 0 ∧
        (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧
        (Nivat.R2.face S₁ n cmax).Nonempty ∧
        Q = S₁.filter fun z => inner2 n z < cmax) ∧
      det u u' ≠ 0 ∧
      -- `u' = v_{ℓ'}` is **primitive**.  `b3_colle2.txt:351` fixes the convention once, in
      -- running text rather than a `Definition` environment: "where `v_ℓ ∈ ℓ ∩ ℤ²` denotes the
      -- non-zero vector parallel to `ℓ` of minimum norm."  Claim 4.7's edge induction
      -- (`b3_colle2.txt:844`) consumes it: with `u' = k • v`, `k ≥ 2`, the ray `g + t • u'`
      -- skips `k - 1` of every `k` lattice points of the `ℓ'`-edge, so the translate
      -- `S + (t+1) • u'` has edge points outside `R ∪ (ray already proved)` and the induction
      -- does not close.  The four conjuncts that mention `u'` above (`inner2 n u' = 0`,
      -- `det u u' ≠ 0`, `IsRegion R u u'`, `hline`) are all invariant under `u' ↦ 2 • u'`,
      -- so primitivity is *not* derivable from them and has to be exported here.
      Primitive u' ∧
      P ξ S₁ ≤ P ξ Q + pw ∧
      (∀ g ∈ B, ∀ i : ℕ, i < pw → g + (i : ℤ) • u' ∈ Q) ∧
      c ≠ 0 ∧
      Colle41.PeriodOn ξ' R (c • u) ∧
      Colle41.IsRegion R u u' ∧
      R ⊂ R' ∧
      ¬ Colle41.PeriodOn ξ' R' (c • u) ∧
      (∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R) ∧
      -- **Conjunct 14 (the `t • u'`-inert straddle) was deleted 2026-09-18.**  It was dead at
      -- kernel level: L2 (`case1_claim47_semiAmbiguous`) took it as `hS_straddle` and never
      -- referenced it, which the build's own unused-variable linter reported.  Deleted rather
      -- than kept beside a corrected version so the straddle is not stated twice, once inertly.
      -- Its content now lives in `S₁` itself: the translate *is* the straddle witness.
      -- `R'` is `𝓡^{N+1}_I`, **not** an arbitrary superset of `R`: Figure 11(B)
      -- (`b3_colle2.txt:850-854`) — since `Ŝ_φ` is `η`-generating, knowing the configuration
      -- on `𝓡^N_I ∪ {g + t·v_{ℓ'} : t ≥ t₀}` pins it on `𝓡^{N+1}_I`, and *that* is what
      -- contradicts the maximality of `N` at `:854`.
      -- Without this conjunct the three `R'`-conjuncts above are discharged by `R' := Set.univ`
      -- for every non-periodic `ξ` (kernel-checked, `tmp/L1_claim46.lean`,
      -- `maximality_export_vacuous`), and L2 would then be quantifying over an `R'` for which
      -- Collé's maximality contradiction does not exist — i.e. L2 would not be Claim 4.7.
      (∀ g ∈ S₁, g ∉ Q → ∀ t₀ : ℤ, τ ≤ t₀ →
        Colle41.PeriodOn ξ' R (c • u) →
        (∀ t : ℤ, t₀ ≤ t → ξ' (t • u' + g + c • u) = ξ' (t • u' + g)) →
        Colle41.PeriodOn ξ' R' (c • u)) ∧
      -- Some baseline point carries a full translate of the generating set inside `R`.
      -- Stated over all of `S₁` rather than over `S₁.erase g`: the vertex `g` is chosen
      -- inside L2/L3, so L1 cannot mention it.  Consumers specialise via `S₁.erase g ⊆ S₁`.
      --
      -- **Weakened 2026-09-19** from `∃ b ∈ B, ∀ z ∈ S₁, b + z ∈ R`: the covering point and
      -- the inhabitant of `B` are now decoupled.  Four independent measurements forced it —
      -- no on-chain consumer ever destructured the coupling (L1asm); it is unsatisfiable when
      -- `S₁` is a singleton, since `derivedQ`'s strict `<` empties the baseline
      -- (`L1Residual.not_maxBResidual_of_singleton`); and it is not derivable from the twelve
      -- conjuncts `L1Straddle.SideData` packages (`conj16_strong_not_free_of_side`).
      (B.Nonempty ∧ ∃ b, ∀ z ∈ S₁, b + z ∈ R) ∧
      -- **The baseline `B` is L1's own maximal one, named.**  Added 2026-09-19 to close
      -- `case1_seed`.  Every conjunct above treats `B` as an opaque finset; this one says what
      -- L1 actually built it from, which is the only fact that lets L3 measure its width.
      --
      -- It costs leaf L1 nothing: `L1Data.ofMaxB` constructs `B` as literally
      -- `maxB (derivedQ ε u' S₁) u' pw` with `pw` literally `(topFace ε u' S₁).card - 1`, so
      -- the field discharges by `⟨ε, rfl, rfl⟩` and `MaxBResidual` is **not** strengthened —
      -- its field count is unchanged.  This is a free export, not a new obligation.
      --
      -- ⚠ The `ε : Bool` must stay existential.  It selects which of the two `u'`-parallel
      -- faces is taken as the top, and L1 chooses it (`b3_colle2.txt:626`'s WLOG); a consumer
      -- that pinned `ε := true` would be asserting L1 always picks the same side, which is
      -- false.  `case1_seed` consumes it by `obtain`, never by `decide`.
      (∃ ε : Bool, pw = (L1Data.topFace ε u' S₁).card - 1 ∧
        B = L1Data.maxB (L1Data.derivedQ ε u' S₁) u' pw) :=
  (exists_L1Data hξ d hℓ_nel hℓ_pos hℓ_neg hxper hgen hSgen hp_mem hp_ne hvl_ne hvl_prim
    hdet_vl hdet_ℓ hdef hcase1).some.toConclusion

/-- **L2 — Claim 4.7** (`b3_colle2.txt:822-852`): `T^u η` is `(ℓ', 𝒯, +)`-semi-ambiguous.

Runs on the maximality of `N` exported by L1: if semi-ambiguity failed, the generating
property of the translates of `𝒮` and of `𝒮_φ` would propagate the period `h = c • u` from
`𝓡^N_I` to `𝓡^{N+1}_I`, contradicting `hnonper_R'`. -/
theorem case1_claim47_semiAmbiguous
    (hξ : IsMinimalCounterexample ξ)
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    {ξ' : Config ℤ} (hξ' : ξ' ∈ orbitClosure ξ)
    {u u' : ℤ × ℤ} {Q : Finset (ℤ × ℤ)} {τ : ℤ} {R R' : Set (ℤ × ℤ)} {c : ℤ}
    (hQS : Q ⊆ S) (hdet : det u u' ≠ 0) (hc : c ≠ 0)
    -- `u' = v_{ℓ'}` is primitive (`b3_colle2.txt:351`), exported by L1.  Consumed by the
    -- edge induction of `b3_colle2.txt:844`: a non-primitive `u'` makes the ray skip edge
    -- lattice points and the induction does not close.
    (hu'_prim : Primitive u')
    -- `Q = S ∖ ℓ'_S` (`b3_colle2.txt:822`).  Supplies the ray seed `g ∈ 𝒯 ∩ ℓ'_𝒯` of `:844`.
    -- `n ≠ 0` rules out the degenerate `Q = ∅` branch admitted by the other four conjuncts
    -- (see the matching comment in `case1_claim46_and_selection`); with it in hand the edge
    -- `S ∖ Q` is a genuine face and both of Collé's `:840` branches are reachable.
    (hQ_edge : ∃ (n : ℝ × ℝ) (cmax : ℝ),
      n ≠ 0 ∧
      inner2 n u' = 0 ∧
      (∀ z ∈ S, inner2 n z ≤ cmax) ∧
      (Nivat.R2.face S n cmax).Nonempty ∧
      Q = S.filter fun z => inner2 n z < cmax)
    (hRper : Colle41.PeriodOn ξ' R (c • u))
    (hR_region : Colle41.IsRegion R u u')
    (hRR' : R ⊂ R')
    (hnonper_R' : ¬ Colle41.PeriodOn ξ' R' (c • u))
    -- Figure 11(B) (`b3_colle2.txt:850-854`): `R'` is the *one-step* enlargement `𝓡^{N+1}_I`.
    -- This is the maximality of `N`; `hnonper_R'` alone is vacuous at `R' := Set.univ`
    -- (kernel-checked, `tmp/L1_claim46.lean`).
    (hR'_step : ∀ g ∈ S, g ∉ Q → ∀ t₀ : ℤ, τ ≤ t₀ →
      Colle41.PeriodOn ξ' R (c • u) →
      (∀ t : ℤ, t₀ ≤ t → ξ' (t • u' + g + c • u) = ξ' (t • u' + g)) →
      Colle41.PeriodOn ξ' R' (c • u))
    (hQR : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R) :
    Colle41.SemiAmbiguousAlong ξ ξ' S Q u' τ := by
  classical
  -- Collé argues by contradiction at a single position `t₀` (`b3_colle2.txt:834`).
  intro t₀ ht₀
  by_contra hcon
  push_neg at hcon
  -- (4.5) at `t₀` (`:836`): the whole `S`-window of `ξ'` there is `c•u`-periodic.
  have hbase := Nivat.Claim47.window_period_of_not_ambiguous hξ' hQS hRper hQR ht₀ hcon
  -- The edge `S ∖ Q = ℓ'_𝒮`, with an *integral* normal in place of `hQ_edge`'s real one.
  obtain ⟨n, cmax, hn, hnu, hle, hface, hQdef⟩ := hQ_edge
  obtain ⟨nI, hnI0, hnIu, g₀, hg₀S, hg₀max, hQiff⟩ :=
    Nivat.Claim47.edge_integral_normal hu'_prim.ne_zero hn hnu hle hface hQdef
  -- Its `+u'`-end `g`.  `exists_face_end_data_gen` also returns the lattice-convexity of
  -- `S.erase g`, which is exactly the side condition `IsGeneratingSet` attaches to `g`.
  obtain ⟨g, hgS, hgerase, hgtop, hgedge⟩ :=
    exists_face_end_data_gen hSgen.1 hSgen.2.1 hu'_prim hnI0 hnIu
  have hlevel : Nivat.LE2.dot nI g = Nivat.LE2.dot nI g₀ :=
    le_antisymm (hg₀max g hgS) (hgtop g₀ hg₀S)
  have hgQ : g ∉ Q := by
    intro hmem
    have h := (hQiff g hgS).mp hmem
    rw [hlevel] at h
    exact lt_irrefl _ h
  -- Every other window point off `Q` sits *behind* `g` on the ray, at `g - k•u'`.
  have hedge : ∀ z ∈ S, z ∉ Q → ∃ k : ℕ, z = g - (k : ℤ) • u' := by
    intro z hzS hzQ
    have hge : Nivat.LE2.dot nI g₀ ≤ Nivat.LE2.dot nI z :=
      not_lt.mp fun h => hzQ ((hQiff z hzS).mpr h)
    rw [← hlevel] at hge
    exact hgedge z hzS (le_antisymm (hgtop z hzS) hge)
  have hgen : Nivat.Colle.GeneratesAt ξ S g := hSgen.2.2 g hgS hgerase
  have hSseg := Nivat.Claim47.hSseg_of_latticeConvex (u' := u') hSgen.2.1 hgS
  -- The `η`-generating induction along the ray (`:844`, Figure 11(A)).
  have hray :=
    Nivat.Claim47.ray_period_of_window_period hξ' hgen hedge hSseg hRper hQR ht₀ hbase
  -- Figure 11(B): that ray upgrades `𝓡^N_I` to `𝓡^{N+1}_I`, against the maximality of `N`.
  exact hnonper_R' (hR'_step g hgS hgQ t₀ ht₀ hRper hray)

/-- The length-`0` word set is a singleton: `Fin 0 → β` has one element and the position set
`{t | τ ≤ t}` is nonempty.  Stated because `wordsFrom`'s `ncard` bound is vacuously wrong at
`p = 0`, which is the content of `pos_pw_of_semiAmbiguous` below. -/
theorem wordsFrom_zero_ncard {β : Type*} (y : ℤ → β) (τ : ℤ) :
    (Colle41.wordsFrom y τ 0).ncard = 1 := by
  have h : Colle41.wordsFrom y τ 0 = {Colle41.wordAt y 0 τ} := by
    ext w
    constructor
    · rintro ⟨t, -, rfl⟩
      exact Set.mem_singleton_iff.mpr (funext fun l => absurd l.isLt (Nat.not_lt_zero _))
    · rintro rfl
      exact ⟨τ, le_refl τ, rfl⟩
  rw [h, Set.ncard_singleton]

/-- **`0 < pw` is free.**

`pw` is Lemma 4.1's pattern width (Collé's `p`).  It was repeatedly treated as an extra
assumption someone would have to export — OPEN #5 asks whether `0 < pw` is equivalent to
`2 ≤ |face|`, and L3band's seed analysis reduced the seed-inside-`R` obligation to "L1's
conjunct 14 **plus** `0 < pw`".  Neither is needed: `0 < pw` follows from the two hypotheses
the sweep already has.

The mechanism is that `pw = 0` is not merely unhelpful but *contradictory*.  Claim 4.2's
counting chain (`Lemma41.lean:595-599`) sends
`(wordsFrom _ τ pw).ncard ≤ P η S - P η Q ≤ pw`, so at `pw = 0` it forces `ncard ≤ 0`; but
the length-`0` word set is a singleton.  So `hdef` and `hamb` are jointly unsatisfiable at
`pw = 0`, and positivity is a case split rather than an export.

⚠ This does **not** settle OPEN #5, which asks for the *equivalence* with `2 ≤ |face|`.  It
settles only the direction that was being treated as an obligation. -/
theorem pos_pw_of_semiAmbiguous {A : Type*} {η x : Config A}
    (hfinη : (Set.range η).Finite) (hx : x ∈ orbitClosure η)
    {S Q : Finset (ℤ × ℤ)} (hQS : Q ⊆ S) {u' g : ℤ × ℤ} {τ : ℤ} {pw : ℕ}
    (hdef : P η S ≤ P η Q + pw)
    (hline : ∀ i : ℕ, i < pw → g + (i : ℤ) • u' ∈ Q)
    (hamb : Colle41.SemiAmbiguousAlong η x S Q u' τ) : 0 < pw := by
  rcases Nat.eq_zero_or_pos pw with rfl | h
  · obtain ⟨-, hcard⟩ :=
      Colle41.wordsFrom_ncard_le_of_semiAmbiguous (p := 0) (g := g) hfinη hx hQS hdef hline hamb
    rw [wordsFrom_zero_ncard] at hcard
    exact absurd hcard (Nat.not_succ_le_zero 0)
  · exact h

/-- `0 < pw` in exactly the hypothesis shape `case1_sweep` offers: `hline` there is
quantified over `B`, and `hB_covers_window` supplies the inhabitant of `B` that
`pos_pw_of_semiAmbiguous` needs. -/
theorem pos_pw_of_case1_hyps {A : Type*} {η x : Config A}
    (hfinη : (Set.range η).Finite) (hx : x ∈ orbitClosure η)
    {S Q B : Finset (ℤ × ℤ)} (hQS : Q ⊆ S) {u' : ℤ × ℤ} {τ : ℤ} {pw : ℕ}
    (hdef : P η S ≤ P η Q + pw)
    (hline : ∀ g ∈ B, ∀ i : ℕ, i < pw → g + (i : ℤ) • u' ∈ Q)
    (hBne : B.Nonempty)
    (hamb : Colle41.SemiAmbiguousAlong η x S Q u' τ) : 0 < pw := by
  obtain ⟨g, hg⟩ := hBne
  exact pos_pw_of_semiAmbiguous hfinη hx hQS hdef (hline g hg) hamb

/-- `Â_∞ ⊆ Â_∞^{(ε)}` for every `ε`: the `t = 0` case of the shell formula, with the
half-plane bound `c_J ≤ dot n_J g` weakened to `c_J - ε ≤ dot n_J g`. -/
theorem ahat_subset_shellInf (cg : ChainDataGeom ξ xper vl p S gen) (ε : ℕ) :
    (⋃ i, cg.toChainData.Ahat i) ⊆ cg.toChainData.shellInf ε := by
  rw [cg.toChainDataWithShell.shellInf_eq ε]
  exact Nivat.MaxEnv.subset_shell ε fun g hg =>
    (cg.toChainDataWithShell.ahat_halfPlane g hg : _)

/-- **`Â_∞` itself is an `(p, v_J)`-region**, given the two binders
`region_periods_and_rays` already takes.

This is the repair for `ShellConvex.not_forall_isLatticeConvexRegion_shellInf_of_hRconv`
(Cconv, 2026-09-19, kernel): `IsLatticeConvexRegion (shellInf ε)` is **false** in general,
and stays false after granting `hRconv`.  So leaf C cannot instantiate the sweep at
`R := shellInf ε`.

It does not have to.  The sweep's conclusion is `∃ K ⊆ R, …`, and C's conclusion asks only
for `R ⊆ shellInf ε`, so **any** lattice-convex sub-region of the shell serves — and
`Â_∞ = ⋃ i, Ahat i` is one, by `ahat_subset_shellInf` above.  Its three `IsRegion` conjuncts
are all already in hand:

* lattice-convexity is `hRconv`, a binder `region_periods_and_rays` takes verbatim;
* the `p`-ray is `cg.rec_p` (`ChainGeom.lean:109`) iterated by `ray_of_recession`;
* the `v_J`-ray is `cg.rec_vJ` (`ChainGeom.lean:136`), likewise.

Both recession fields are stated about `⋃ i, Ahat i` and **not** about any shell, which is
exactly why the shell was the wrong set to ask about. -/
theorem isRegion_iUnion_Ahat (cg : ChainDataGeom ξ xper vl p S gen)
    (hRconv : IsLatticeConvexRegion (⋃ i, cg.toChainData.Ahat i))
    (hRne : (⋃ i, cg.toChainData.Ahat i).Nonempty) :
    Colle41.IsRegion (⋃ i, cg.toChainData.Ahat i) p cg.vJ := by
  obtain ⟨w, hw⟩ := hRne
  exact ⟨hRconv, ⟨w, fun k => ray_of_recession cg.rec_p hw k⟩,
    ⟨w, fun k => ray_of_recession cg.rec_vJ hw k⟩⟩

/-- **The seed — the whole of what `case1_sweep` still owes, in its 2026-09-19 repaired
shape.**

`case1_sweep` used to be a thirteen-hypothesis blob with a `sorry` body.  L3band's §23–§31
(`L3Band.lean`) reduced Collé's sweep to a single unproduced binder, and this declaration is
that binder, stated on the main chain so it can be attacked by name.  Everything else the
sweep needs — the band, the level enumeration, the cross-level window clause, the vertex
selection in *both* orientations, and the WLOG that makes `u` primitive — is proved and
kernel-clean in `L3Band.lean`.

**What it says now: `B` is wide enough.**  `HasBlock u u' B m` (`L3Band.lean:2688`) asks that
`B` contain, on each of the `|det u u'|` residue classes of the `u`-level function
`⟪(-u.2, u.1), ·⟫`, a point whose forward `u`-run of length `m` stays in `B`.  The width
demanded is `min (Wrow fr S aLo) (Wrow fr S aHi)` — the *smaller* of the two extreme rows of
`S`, because L3band now has the sweep in both directions and `seed_of_block` may take
whichever is narrower.

Note what is **not** here any more: no `ξ'`, no `q`, no `t₀`, no `R`, no row positions.  This is
a finite combinatorial statement about `B` and `S`.  That is the point of the repair — it is
exactly the obligation L1 can discharge from `maxB`, and L1asm has priced it (the multi-level
`maxB` theorem, `L1Assemble.lean`).

**Why the full hypothesis list is still carried.**  Every binder of `case1_sweep` is repeated
verbatim.  They are not all needed — `hline` plus `0 < pw` plus `hdef41`/`hamb` are what a
producer will actually use — but a `sorry` with *more* hypotheses is a *weaker* obligation, so
carrying them costs nothing and keeps the call site below unchanged if the producer needs one.

⚠ **This is a split, not a discharge.**  `sorry TOTAL` is unchanged.

## §14 record — the previous statement of `case1_seed` was DEFECTIVE and has been replaced

Retained here rather than in history because the failure mode recurs.  Between 2026-09-19
05:23 and this rewiring, `case1_seed` asked for agreement on `rowLine fr b₀ cQ q (Wsup fr S a)
r i`, with `cQ` a **universal** binder and the row base pinned to `m₀ + i · Wsup`.  Three
independent defects, none of which the kernel could see — **a `sorry` body accepts whatever is
stated** (the same failure mode as this file's earlier `t • v_J + Q ⊆ Â_∞` obligation, which
was geometrically false and compiled cleanly):

1. `cQ` universal.  The agreement trace exists only at levels
   `≥ max_{g ∈ B} ⟪ny, g⟫ + (τ + pw) · ⟪n, u'⟫`; below that no binder says anything.
   **Repaired** in `L3Band.LineSeed` (`:2678`) by `∃ cQ`, chosen by the seed's producer.
2. Row position pinned.  Moving a run to the `rowLine` position uses `hRper` shifts of `c • u`,
   which reach only positions `≡ trace (mod c)`.  **Repaired** by a per-line base
   `m₀ : ℕ → ℤ`, existential, with stagger `m₀ i + W ≤ m₀ (i + 1)`.
3. Collé's flipped case (`b3_colle2.txt:702-706`) was not expressible: sweeping downward forces
   the vertex onto the `−u'`-side `u`-edge, and when that edge is the longer one the seed is
   too narrow.  **Repaired** by `sweep_conclusion_up_of_lineSeed` plus the `min` above, so the
   construction may take the shorter edge either way.

⚠ The old docstring also warned "it must not be closed by redefining `Wrow` as the min — that
would formalise something weaker than the paper".  That warning is **withdrawn**, and the
reason matters: the `min` here is not a redefinition of `Wrow`, it is a *disjunction of two
proved sweeps* (`sweep_conclusion_of_generatingSet_of_block` discharges either branch of
`min_le_iff`).  Collé's WLOG at `:626` takes the shorter edge for the same reason.

**2026-09-19 update — the bridge is compiled, and in a different shape than was asked for.**
The line above used to say the bridge `Wrow fr S aLo = (bottomFace …).card - 1` was open.  The
per-side equality it names is **false in general**: `aLo` is a vertex of the `fr.n`-minimal
face, and nothing forces the `u`-run through it to be the *shorter* of the two `u`-edges.  What
is true, and is now proved as `L3Band.min_Wrow_eq_min_card_face` (`L3Band.lean:3387`,
`#print axioms` clean), is the **min** form

    min (Wrow fr S aLo) (Wrow fr S aHi)
      = min (L1Data.topFace true u S).card (L1Data.bottomFace true u S).card - 1

which is exactly the quantity `L1Data.maxB_wide_levels` (`L1Assemble.lean:1530`) delivers as its
block height.  So both conjuncts of this theorem's conclusion have kernel producers and the
residual obligation is *routing*, not mathematics: what is still missing is L1's `hBmax` export
(`∃ ε, pw = (topFace ε u' S).card - 1 ∧ B = maxB (derivedQ ε u' S) u' pw`) threaded to this
binder list.  The body it enables is compiled in `tmp/tl_case1_seed_probe.lean` — ⚠ **in
`tmp/`, not landed**, and a `tmp/` receipt is debt, not progress, until this `sorry` is gone. -/
theorem case1_seed
    (hξ : IsMinimalCounterexample ξ)
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    {ξ' : Config ℤ} (hξ' : ξ' ∈ orbitClosure ξ)
    {u u' : ℤ × ℤ} {Q : Finset (ℤ × ℤ)} {τ : ℤ} {pw : ℕ} {B : Finset (ℤ × ℤ)}
    {R : Set (ℤ × ℤ)} {c : ℤ}
    (hQS : Q ⊆ S) (hdet : det u u' ≠ 0) (hc : c ≠ 0)
    (hu_prim : Primitive u) (hu'_prim : Primitive u')
    (hdef41 : P ξ S ≤ P ξ Q + pw)
    (hline : ∀ g ∈ B, ∀ i : ℕ, i < pw → g + (i : ℤ) • u' ∈ Q)
    (hRper : Colle41.PeriodOn ξ' R (c • u))
    (hR_region : Colle41.IsRegion R u u')
    (hQR : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R)
    -- **Weakened 2026-09-19 (integrator).**  Was `∃ b ∈ B, ∀ z ∈ S, b + z ∈ R`.  The body below
    -- uses the two halves *separately* — `B.Nonempty` for `pos_pw_of_case1_hyps`, and nothing
    -- at all from the covering — so tying them to one `b` was never load-bearing here.  Cclaim
    -- measured what the strong form costs leaf C: with `b ∈ B ⊆ Q` (`hline`, `0 < pw`) the
    -- covering forces an absolute window-height condition `dot nJ q - dot nJ a₀ ≥ ε + 2 - cJ`
    -- on Lemma 2.4's `Sgen`, and Lemma 2.4 says nothing about size, so nothing in the tree
    -- produces it.  This is a strict weakening of a hypothesis, i.e. a **strengthening** of
    -- this theorem; the kernel checks it, the `sorry` does not.
    (hB_covers_window : B.Nonempty ∧ ∃ b, ∀ z ∈ S, b + z ∈ R)
    (hamb : Colle41.SemiAmbiguousAlong ξ ξ' S Q u' τ)
    (fr : Nivat.L3Band.LevelFrame u u') (aLo aHi : ℤ × ℤ)
    (haLo : aLo ∈ S) (haHi : aHi ∈ S)
    (hvertLo : ∀ b ∈ S.erase aLo,
      Nivat.LE2.dot fr.n aLo < Nivat.LE2.dot fr.n b ∨
        (Nivat.LE2.dot fr.n aLo = Nivat.LE2.dot fr.n b ∧
          Nivat.LE2.dot fr.d' b < Nivat.LE2.dot fr.d' aLo))
    (hvertHi : ∀ b ∈ S.erase aHi,
      Nivat.LE2.dot fr.n b < Nivat.LE2.dot fr.n aHi ∨
        (Nivat.LE2.dot fr.n b = Nivat.LE2.dot fr.n aHi ∧
          Nivat.LE2.dot fr.d' b < Nivat.LE2.dot fr.d' aHi))
    (hBmax : ∃ ε : Bool, pw = (L1Data.topFace ε u' S).card - 1 ∧
      B = L1Data.maxB (L1Data.derivedQ ε u' S) u' pw) :
    ∃ m : ℕ, Nivat.L3Band.HasBlock u u' B m ∧
      min (Nivat.L3Band.Wrow fr S aLo) (Nivat.L3Band.Wrow fr S aHi) ≤ m := by
  have hpw : 0 < pw :=
    pos_pw_of_case1_hyps hξ.1.1 hξ' hQS hdef41 hline hB_covers_window.1 hamb
  obtain ⟨ε, hpw', hB⟩ := hBmax
  refine ⟨_, ?_, (Nivat.L3Band.min_Wrow_eq_min_card_face fr hSgen.2.1 hSgen.1 hu_prim
    haLo haHi hvertLo hvertHi).le⟩
  rw [hB, hpw']
  exact Nivat.L3Band.hasBlock_maxB hSgen.2.1 hSgen.1 hu_prim hu'_prim hdet ε (by omega)

/-- **L3 — the sweep hypothesis** of Lemma 4.1 (`Lemma41.lean:776-779`).

`lemma41_colle_region_shape` takes this as a full assumed hypothesis rather than deriving it;
discharging it is the third hard input of Case 1, alongside Claims 4.6 and 4.7.  Collé's
argument is the pigeonhole of `:700` followed by the line-by-line sweep of Claim 4.3
(`:680-698`). -/
theorem case1_sweep
    (hξ : IsMinimalCounterexample ξ)
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    {ξ' : Config ℤ} (hξ' : ξ' ∈ orbitClosure ξ)
    {u u' : ℤ × ℤ} {Q : Finset (ℤ × ℤ)} {τ : ℤ} {pw : ℕ} {B : Finset (ℤ × ℤ)}
    {R : Set (ℤ × ℤ)} {c : ℤ}
    (hQS : Q ⊆ S) (hdet : det u u' ≠ 0) (hc : c ≠ 0)
    -- `u' = v_{ℓ'}` is primitive (`b3_colle2.txt:351`), exported by L1 and already bound at the
    -- call site (`:1125`).  Restored 2026-09-18: the sweep of Claim 4.3 (`:680-698`) walks the
    -- lattice points of each `ℓ'`-line one step at a time, and a non-primitive `u'` skips some,
    -- exactly as in `case1_claim47_semiAmbiguous`'s edge induction — which is now proved and
    -- does consume it (`Claim47Core.lean`, `exists_face_end_data_gen`'s `Primitive d`).
    (hu'_prim : Primitive u')
    (hdef41 : P ξ S ≤ P ξ Q + pw)
    (hline : ∀ g ∈ B, ∀ i : ℕ, i < pw → g + (i : ℤ) • u' ∈ Q)
    (hRper : Colle41.PeriodOn ξ' R (c • u))
    (hR_region : Colle41.IsRegion R u u')
    -- **L1's conjunct 14** (`L1Data.lean:128`), added to this signature 2026-09-18.
    --
    -- This costs the caller nothing: `region_case1` already binds it under this very name when
    -- it destructures L1's export (`:1199`), and already consumes it one line later for Claim
    -- 4.7 (`:1206`).  It was simply never passed here.
    --
    -- It is not redundant.  L3band measured (`L3Band.lean`, `sweptSeed_subset_R` → `:304`
    -- `halfStripFrom_subset_R`) that the seed-inside-`R` obligation reduces to exactly this
    -- statement plus `0 < pw`, and that **nothing else in this hypothesis list connects `Q` to
    -- `R`**: `hamb` unfolds to `SemiAmbiguousAlong` (`Lemma41.lean:540-544`), which mentions no
    -- `R` at all; `hQS` is only `Q ⊆ S`; and `hB_covers_window` pins finitely many points while
    -- the half-strip is unbounded in `t`.  ⚠ That is "no other connection in the list", not
    -- "underivable" — L3band did not claim the stronger thing and neither do I.
    (hQR : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • u' + z ∈ R ∧ t • u' + z + c • u ∈ R)
    (hB_covers_window : B.Nonempty ∧ ∃ b, ∀ z ∈ S, b + z ∈ R)
    (hamb : Colle41.SemiAmbiguousAlong ξ ξ' S Q u' τ)
    -- Passed straight through to `case1_seed`.  Safe across this theorem's WLOG
    -- (`L3Band.case1_sweep_conclusion_wlog_primitive`, applied at `:1362`): that rescale
    -- rebinds only `u ↦ u₀` and `c ↦ c₀`, and `hBmax` mentions neither — `maxB (derivedQ ε u'
    -- S) u' pw` is built entirely from `u'`, `S` and `pw`.  Had the baseline instead been
    -- exported as a `HasBlock` at L1's own `u`, it would **not** survive this line, because
    -- both the level index and the run step rescale with `u`.
    (hBmax : ∃ ε : Bool, pw = (L1Data.topFace ε u' S).card - 1 ∧
      B = L1Data.maxB (L1Data.derivedQ ε u' S) u' pw) :
    ∀ q : ℕ, 0 < q →
      (∀ g ∈ B, ∀ t : ℤ, τ + (pw : ℤ) ≤ t → ξ' (g + (t + (q : ℤ)) • u') = ξ' (g + t • u')) →
      ∃ K : Set (ℤ × ℤ), K ⊆ R ∧ Colle41.IsRegion K u u' ∧ K.Nonempty ∧
        ∃ t₀ : ℕ, 0 < t₀ ∧ Colle41.PeriodOn ξ' K (((t₀ * q : ℕ) : ℤ) • u') := by
  intro q hq hladder
  refine Nivat.L3Band.case1_sweep_conclusion_wlog_primitive hdet hc hRper hR_region hQR q ?_
  intro u₀ c₀ hprim hdet₀ hc₀ hRper₀ hreg₀ hQR₀
  have hfin : (Set.range ξ').Finite := BL.finite_range_of_mem_orbitClosure hξ.1.1 hξ'
  obtain ⟨hBne, b, hbS⟩ := hB_covers_window
  obtain ⟨z₀, hz₀⟩ := hSgen.1
  -- `0 < pw` is not a binder of this theorem and not a field of `L1Data`; it is *derived*
  -- here from semi-ambiguity plus the complexity deficit (`pos_pw_of_case1_hyps`, `:1201`),
  -- with `hB_covers_window` supplying the inhabitant of `B`.
  have hpw : 0 < pw :=
    pos_pw_of_case1_hyps hξ.1.1 hξ' hQS hdef41 hline hBne hamb
  have hBQ : ∀ g ∈ B, g ∈ Q := Nivat.Colle43.subset_Q_of_hline hpw hline
  have hτ : τ ≤ τ + (pw : ℤ) := by omega
  obtain ⟨fr, aLo, aHi, haLo, haHi, hvertLo, hvertHi, himp⟩ :=
    Nivat.L3Band.sweep_conclusion_of_generatingSet_of_block hfin hξ' hSgen hprim hdet₀
      hreg₀ hc₀ hRper₀ hτ hBQ hQR₀ hq hladder (hbS z₀ hz₀)
  obtain ⟨m, hB, hm⟩ :=
    case1_seed hξ hSgen hξ' hQS hdet₀ hc₀ hprim hu'_prim hdef41 hline hRper₀ hreg₀ hQR₀
      ⟨hBne, b, hbS⟩ hamb fr aLo aHi haLo haHi hvertLo hvertHi hBmax
  exact himp m hB hm

/- **L4 — Claim 4.8** (`b3_colle2.txt:862`) used to sit here, as
`case1_claim48_no_fully_periodic_acc`, and was deleted 2026-09-18 together with L1's export
`∃ I : Fin d.m, det u' (d.h I) = 0` that fed it.

Why it is gone rather than open.  It discharged the *weakened* first clause of `region_case1`,
`¬ ∃ y, IsFullyPeriodic y ∧ (y is a limit along u' of translates of ξ')`, which was never what
this branch owed: `region_case1` now returns `¬ IsPeriodic ξ'`, and in Case 1 that is
`b3_colle2.txt:846` verbatim — *"since `T^u η` is a non-periodic configuration"* — because `ξ'`
**is** a translate `T^e ξ` (L1's `∃ e, ξ' = T e ξ`, from `Case1` at `:326-328`) and `ξ` is
non-periodic by `hξ.1.2.2.1`.  One line, no Lemma 4.4.

Collé does prove Claim 4.8, and needs it: it feeds his Claims 4.9/4.10, which run the §4
contradiction.  Our interface to §8 is `colle_region`, which asks only for `¬ IsPeriodic ξ'`
plus the region, so that part of his §4 is not on our path.  ⚠ **Case 2 is not like this.**
There `ϑ` comes from Lemma 3.5 and is not a translate of `ξ`, so Claim 3.7
(`region_not_periodic`) stays live and feeds `Claim414.claim414` — see `ColleRegion.lean`'s
Case 2 branch.  Deleting the Case 1 analogue does not license deleting that one. -/

/-- **Lemma 4.5, Case 1** (`b3_colle2.txt:780-884`), packaged as the conclusion of
`colle_region`.

Collé's chain in this branch, read off the source:

* **Claim 4.6** (`:780`): `(T^u η)|𝓡_{ι−1}` is periodic with period `h ∥ ℓ`, where
  `𝓡_{ι−1} := {g + t·v_{ℓ_{ι−1}} : g ∈ H_B(ℓ), t ∈ ℤ₊}` is an `(−ℓ, ℓ_{ι−1})`-region (`:784`).
  Proved (`:788-804`) by working modulo a prime `p` with `𝒜 ⊂ ℤ_p`, dropping the summand
  `η̄_{ι₀}` of the periodic decomposition, and using that `𝒮_{φ_ι}` has no edge parallel to
  `±ℓ` (Lemma 2.6) to push the periodicity across the lines `l₁, l₂, …` one at a time.
* `:806-814`: the nested regions `𝓡_{ι−1} ⊂ ⋯ ⊂ 𝓡_{ι−m+1}`, and `I` the **smallest** index
  with `(T^u η)|𝓡_I` of period `h`.  `I` exists because `(T^u η)|ℋ(ℓ_{ι−m})` has no period
  parallel to `ℓ_{ι−m}` or `ℓ` — otherwise Proposition 2.12 makes `T^u η` periodic.
* `:816-820`: `𝓡^n_I` sliced by `dist(·, ℓ'_{𝓡_I}) ≤ d_n`, with `⋃_n 𝓡^n_I = 𝓡_{I−1}`, and
  `N` the **greatest** index with `(T^u η)|𝓡^N_I` of period `h`.
* **Claim 4.7** (`:822-852`): `T^u η` is `(ℓ', 𝒯, +)`-semi-ambiguous for every translate `𝒯`
  of `𝒮` with `𝒯 \ ℓ'_𝒯 ⊂ 𝓡^N_I` but `𝒯 ⊄ 𝓡^N_I`; otherwise the generating property of `𝒯`
  and of `𝒮_φ` propagates the period `h` to `𝓡^{N+1}_I`, contradicting maximality of `N`.
* `:860`: **Lemma 4.1** then gives an `(−ℓ, ℓ')`-region `𝒦 ⊂ 𝓡^N_I` on which `T^u η` is
  fully periodic, with one period `∥ ℓ` and another `∥ ℓ'`.
* **Claim 4.8** (`:862`): `{T^{t·v_{ℓ'}}(T^u η) : t ∈ ℤ₊}` has no fully periodic accumulation
  point — by **Lemma 4.4** (`:711`) applied to `T^u η`, which is non-periodic and carries a
  `ℤ`-minimal periodic decomposition.  This is the Case 1 counterpart of Claim 3.7; note it
  is a *different* argument, and a more elementary one.

Both sets are genuinely needed here, so both are inputs: `d.Sphi = 𝒮_φ` (through `d`) for
`hcase1` and for Claim 4.6's `𝒮_{φ_ι} ⊆ 𝒮_φ` (`:790-792`), and the Lemma 2.4 set `S`
(`hgen`/`hSgen`/`hdef`) for Claim 4.7's translates of `𝒮` (`:824`).

`ξ' := T u ξ`, `vl' := v_{ℓ'}` and `R := 𝒦` are what this theorem returns.  The endgame
`:860` is `Nivat.Colle41.lemma41_colle_region_shape` (`Lemma41.lean:767`, `sorry`-free),
whose conclusion is the region clause below up to Lemma 4.1's extra conjunct `K ⊆ R`.
Its hard inputs are three, not two: `hamb` (Claim 4.7), `hRper` (Claim 4.6) and `hsweep`
(`Lemma41.lean:776-779`), a full assumed hypothesis rather than a derived one; on top of
these, the selection of `I` and `N` (`:806-820`) belongs to neither claim. -/
theorem region_case1 (hξ : IsMinimalCounterexample ξ) (d : DecompDataZ ξ)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    -- Passed straight through to `case1_claim46_and_selection` (`:950`); see the note at `:843`.
    (hℓ_pos : Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hxper : xper ∈ orbitClosure ξ) (hgen : Nivat.Colle.GeneratesAt ξ S gen)
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (hp_mem : p ∈ Per xper) (hp_ne : p ≠ 0) (hvl_ne : vl ≠ 0) (hvl_prim : Primitive vl)
    (hdet_vl : det p vl = 0) (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0)
    (hdef : ∀ (n : ℝ × ℝ) (cmax cmin : ℝ),
      (∀ z ∈ S, inner2 n z ≤ cmax) → (Nivat.R2.face S n cmax).Nonempty →
      (∀ z ∈ S, cmin ≤ inner2 n z) → (Nivat.R2.face S n cmin).Nonempty →
        P ξ S - P ξ (S.filter fun z => inner2 n z < cmax) ≤
          (Nivat.R2.face S n cmax).card - 1 ∧
        P ξ S - P ξ (S.filter fun z => cmin < inner2 n z) ≤
          (Nivat.R2.face S n cmin).card - 1)
    (hcase1 : Case1 ξ xper d.Sphi vl) :
    ∃ ξ' ∈ orbitClosure ξ, ¬ IsPeriodic ξ' ∧
      ∃ R : Set (ℤ × ℤ),
        IsLatticeConvexRegion R ∧ R.Nonempty ∧
          ∃ h h' z₀ z₀' : ℤ × ℤ, det h h' ≠ 0 ∧
            (∀ k : ℕ, z₀ + (k : ℤ) • h ∈ R) ∧ (∀ k : ℕ, z₀' + (k : ℤ) • h' ∈ R) ∧
            (∀ z ∈ R, z + h ∈ R → ξ' (z + h) = ξ' z) ∧
            (∀ z ∈ R, z + h' ∈ R → ξ' (z + h') = ξ' z) := by
  -- L1: Claim 4.6 + the `I`/`N` selection give `ξ'`, the translated window `S₁`, and all of
  -- Lemma 4.1's data.  Everything downstream runs on `S₁`, not on the caller's `S`.
  obtain ⟨ξ', hξ'_mem, u, u', Q, τ, pw, B, R, R', c, S₁, hS₁gen, ⟨e, hξ'_eq⟩,
    hQS, hQ_edge, hdet, hu'_prim, hdef41, hline, hc, hRper, hR_region, hRR', hnonper_R', hQR,
    hR'_step, hB_covers, hBmax⟩ :=
    case1_claim46_and_selection hξ d hℓ_nel hℓ_pos hℓ_neg hxper hgen hSgen hp_mem hp_ne hvl_ne
      hvl_prim hdet_vl hdet_ℓ hdef hcase1

  -- L2: Claim 4.7, run on the maximality of `N` that L1 exports.
  have hamb : Colle41.SemiAmbiguousAlong ξ ξ' S₁ Q u' τ :=
    case1_claim47_semiAmbiguous hξ hS₁gen hξ'_mem hQS hdet hc hu'_prim hQ_edge hRper hR_region
      hRR' hnonper_R' hR'_step hQR

  -- L3: the sweep hypothesis.  Since 2026-09-19 `L1Data.hbase` is itself the *weak* conjunct 16
  -- (`B.Nonempty ∧ ∃ b, …`, `L1Data.lean:146`), which is exactly what `case1_sweep` asks for, so
  -- `hB_covers` passes straight through.  The adapter that used to sit here — forgetting `b ∈ B`
  -- out of the strong form — is gone with the coupling it adapted.
  have hsweep := case1_sweep (B := B) hξ hS₁gen hξ'_mem hQS hdet hc hu'_prim hdef41 hline hRper
    hR_region hQR hB_covers hamb hBmax

  -- Assembly: Lemma 4.1 in `colle_region` shape (`Lemma41.lean:767`, `sorry`-free).
  obtain ⟨K, -, hKconv, hKne, h, h', z₀, z₀', hdetK, hray, hray', hper, hper'⟩ :=
    Colle41.lemma41_colle_region_shape hξ.1.1 hξ'_mem hQS hdet hdef41 hline hamb hc hRper
      hsweep

  -- Non-periodicity of `ξ'`: it is a translate of `ξ`, and `ξ` is non-periodic because it is a
  -- counterexample (`hξ.1.2.2.1`, `ExternalDefs.lean:48`).  This is `b3_colle2.txt:846`
  -- verbatim — *"since `T^u η` is a non-periodic configuration"*.
  have hξ'_np : ¬ IsPeriodic ξ' :=
    hξ'_eq ▸ CosetPigeonhole.not_isPeriodic_T_of_not_isPeriodic e hξ.1.2.2.1
  exact ⟨ξ', hξ'_mem, hξ'_np,
    K, hKconv, hKne, h, h', z₀, z₀', hdetK, hray, hray', hper, hper'⟩

/-- The region `Â_∞ = ⋃ i Â_i` is lattice-convex.

Available: `c.envA` gives `Env (c.A i)`, `c.AhatEq` presents `c.Ahat i` as a translate of
`c.A i`, `Nivat.LE2.envOf_shift` transports `Env` across that translate, and `c.AhatMono`
directs the union — all usable only because `hc_env` pins `Env` to `Nivat.LE2.EnvOf ↑S`.

Missing: nothing, since 2026-09-16.  `Nivat.LE2.EnvOf` bundles `IsLatticeConvexRegion`
(via `WeaklyEnveloped`), so `c.envA` gives each `c.A i` directly; the union is then taken
through `LatticeEdges.isLatticeConvexRegion_iUnion_of_mono_fixedEdges_finite`, whose
`sorry` was closed the same day. -/
theorem region_latticeConvex (c : ChainData ξ xper vl S gen)
    (hξ : IsMinimalCounterexample ξ)
    (hxper : xper ∈ orbitClosure ξ)
    (hc_env : c.Env = Nivat.LE2.EnvOf (S : Set (ℤ × ℤ)))
    (hgen : Nivat.Colle.GeneratesAt ξ S gen) :
    IsLatticeConvexRegion (⋃ i, c.Ahat i) := by
  -- Each A i is enveloped, hence lattice-convex by E2's definition
  have hAconv : ∀ i, IsLatticeConvexRegion (c.A i) := by
    intro i
    have henvA := c.envA i
    rw [hc_env] at henvA
    exact henvA.1.1
  -- Each Ahat i is a translate of A i, hence also lattice-convex
  have hAhatconv : ∀ i, IsLatticeConvexRegion (c.Ahat i) := by
    intro i
    rw [c.AhatEq i]
    have : Nivat.LE2.shift (-(c.kk i : ℤ) • vl) (c.A i) = {z | z + (c.kk i : ℤ) • vl ∈ c.A i} := by
      ext z; simp [Nivat.LE2.shift]
    rw [← this]
    exact Nivat.LE2.isLatticeConvexRegion_shift (-(c.kk i : ℤ) • vl) (hAconv i)
  -- The union of nested lattice-convex sets with fixed edges is lattice-convex
  have hAhatfin : ∀ i, (c.Ahat i).Finite := fun i => (c.shellFinite i 0).subset (c.subShell i 0)
  apply Nivat.LE2.isLatticeConvexRegion_iUnion_of_mono_fixedEdges_finite (S := ↑S) c.AhatMono
    hAhatconv hAhatfin
  -- hedge : ∀ i, Nivat.LE2.E (c.Ahat i) = Nivat.LE2.E ↑S
  --   1. `c.AhatEq` presents `Ahat i` as a translate of `A i`, and `E` is shift-invariant.
  --   2. `c.envA i`, read through `hc_env`, says `A i` is `EnvOf ↑S`-enveloped, and
  --      `Enveloped.E_eq` turns that into the edge equality — it wants `(E ↑S).Finite`,
  --      supplied by `finite_E_of_finite` (the `PosArea`-free finiteness lemma; `S` is a
  --      `Finset` and carries no positive-area guarantee).
  intro i
  rw [c.AhatEq i]
  have hshift :
      Nivat.LE2.shift (-(c.kk i : ℤ) • vl) (c.A i) = {z | z + (c.kk i : ℤ) • vl ∈ c.A i} := by
    ext z; simp [Nivat.LE2.shift]
  rw [← hshift, Nivat.LE2.E_shift]
  have henvA := c.envA i
  rw [hc_env] at henvA
  exact Nivat.LE2.Enveloped.E_eq (Nivat.LE2.finite_E_of_finite S.finite_toSet) henvA

/-- The region `Â_∞` is nonempty.

`hc_grow` gives `c.B 0 ⊂ c.B 1`, hence `c.B 1` is inhabited; `c.subBA` puts that point in
`c.A 1`; `c.AhatEq` presents `c.Ahat 1` as a translate of `c.A 1`.  Unlike the others, this
one needs no new mathematics.

## Closed 2026-09-14 --- `Step_Nonempty.lean`

Six tactic lines, exactly the route above: `Set.exists_of_ssubset (hc_grow 0)`, then
`c.subBA 1`, then subtract `(c.kk 1 : ℤ) • vl` to land in `c.Ahat 1`.  `hc_grow` is used only
at index 0, but the signature may not change, so it is taken whole.  Alias substitution
checked by `example : @Nivat.ColleReg.region_nonempty = @Nivat.ColleStep.region_nonempty :=
rfl`; measured closure `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. -/
theorem region_nonempty (c : ChainData ξ xper vl S gen)
    (hc_grow : ∀ i, c.B i ⊂ c.B (i + 1)) :
    (⋃ i, c.Ahat i).Nonempty :=
  Nivat.ColleStep.region_nonempty c hc_grow

/-- **`region_nonempty` at the strength it actually needs** (`Step_Nonempty.lean`,
2026-09-20).  Only `c.B 1` being inhabited is used; the strict-growth family was never
touched beyond index `0`, and even there only its `x ∈ c.B 1` half.  This is what
`exists_chainData`'s consumer now calls. -/
theorem region_nonempty_of_nonempty_B1 (c : ChainData ξ xper vl S gen)
    (hB1 : (c.B 1).Nonempty) :
    (⋃ i, c.Ahat i).Nonempty :=
  Nivat.ColleStep.region_nonempty_of_nonempty_B1 c hB1

/-- **The complement of a strict sublevel set is the exposed face.**

For any `S₁` whose `inner2 n`-values are bounded above by `cmax`, the points of `S₁` that are
*not* in `S₁.filter (inner2 n · < cmax)` are exactly the points of `Nivat.R2.face S₁ n cmax`.

This is the bridge `exists_case2_window` needs between its two edge conjuncts: `hQ_edge` only
*defines* `Q` as a sublevel set, while `hface` and `Claim411.claim411_semiAmbiguous` both speak
about `g ∈ S₁` with `g ∉ Q`.  Without this lemma those are two unrelated descriptions of the
same set. -/
theorem sdiff_filter_lt_eq_face {S₁ : Finset (ℤ × ℤ)} {n : ℝ × ℝ} {cmax : ℝ}
    (hle : ∀ z ∈ S₁, inner2 n z ≤ cmax) :
    S₁ \ S₁.filter (fun z => inner2 n z < cmax) = Nivat.R2.face S₁ n cmax := by
  classical
  ext z
  simp only [Finset.mem_sdiff, Finset.mem_filter, Nivat.R2.mem_face, not_and, not_lt]
  constructor
  · rintro ⟨hz, h⟩
    exact ⟨hz, le_antisymm (hle z hz) (h hz)⟩
  · rintro ⟨hz, he⟩
    exact ⟨hz, fun _ => he.ge⟩

/-- **`exists_case2_window`'s edge conjunct is free once `𝒯` is nonempty.**

The conjunct asks for a real normal `n` with `n ⟂ v_J`, a level `cmax` attained on `S₁` and
bounding it, and `Q` cut out as the strict sublevel set.  There is essentially only one
choice, and it is forced by the *other* conjuncts rather than by this one:

* `n ⟂ v_J` and `⟪n_J, v_J⟫ = 0` (`cg.dot_nJ_vJ`) put `n` and `n_J` both in the line
  orthogonal to `v_J ≠ 0`, so `n` is a real multiple of `n_J`.
* `hface` wants the exposed face `S₁ ∖ Q` to land **outside** `Â_∞^(ε)`, i.e. at *low*
  `⟪n_J, ·⟫`.  So the `n`-maximal face must be the `n_J`-minimal one, which forces the
  multiple to be **negative**.

Hence `n := toReal (-n_J)`, and `cmax` is then just the maximum of `inner2 n` over `S₁`, for
which `L1Data.le_levelMax` and `L1Data.face_levelMax_nonempty` are exactly the two facts
needed.  The `inner2 n z = -⟪n_J, z⟫` conjunct is what lets a consumer convert the resulting
real inequalities back into the integer layer arithmetic that `shellInf` is defined by.

⚠ This settles only the *shape* of the edge.  Whether the exposed face actually straddles —
`hface` — is real mathematics and is **not** touched here; so is the existence of a generating
translate `S₁` in the first place. -/
theorem exists_edge_data (cg : ChainDataGeom ξ xper vl p S gen)
    {S₁ : Finset (ℤ × ℤ)} (hne : S₁.Nonempty) :
    ∃ (n : ℝ × ℝ) (cmax : ℝ),
      n ≠ 0 ∧
      inner2 n cg.vJ = 0 ∧
      (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧
      (Nivat.R2.face S₁ n cmax).Nonempty ∧
      (∀ z : ℤ × ℤ, inner2 n z = -(Nivat.LE2.dot cg.nJ z : ℝ)) ∧
      S₁ \ S₁.filter (fun z => inner2 n z < cmax) = Nivat.R2.face S₁ n cmax := by
  classical
  refine ⟨Nivat.toReal (-cg.nJ), L1Data.levelMax S₁ (Nivat.toReal (-cg.nJ)), ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro h
    have h0 : Nivat.toReal (-cg.nJ) = Nivat.toReal 0 := by
      rw [h]; simp [Nivat.toReal, Prod.ext_iff]
    have := Nivat.toReal_injective h0
    exact cg.nJ_prim.ne_zero (by simpa using neg_eq_zero.mp this)
  · rw [Nivat.LE2.inner2_toReal, Nivat.LE2.dot_neg_left, cg.dot_nJ_vJ]
    simp
  · exact L1Data.le_levelMax hne
  · exact L1Data.face_levelMax_nonempty hne
  · intro z
    rw [Nivat.LE2.inner2_toReal, Nivat.LE2.dot_neg_left]
    push_cast
    ring
  · exact sdiff_filter_lt_eq_face (L1Data.le_levelMax hne)


/-- Translating along `v_J` does not change the `ℓ_J`-layer.  Immediate from
`cg.dot_nJ_vJ`, but it is the reason `exists_case2_window`'s `τ` is a single integer rather
than a function of the window: once the straddle is achieved at one height it holds at all of
them. -/
theorem dot_nJ_vJ_smul_add (cg : ChainDataGeom ξ xper vl p S gen) (t : ℤ) (g : ℤ × ℤ) :
    Nivat.LE2.dot cg.nJ (t • cg.vJ + g) = Nivat.LE2.dot cg.nJ g := by
  rw [Nivat.LE2.dot_add]
  have h : Nivat.LE2.dot cg.nJ (t • cg.vJ) = t * Nivat.LE2.dot cg.nJ cg.vJ := by
    simp only [Nivat.LE2.dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [h, cg.dot_nJ_vJ, mul_zero, zero_add]

/-- **Below the cut-off level, shell membership is impossible.**

`shellInf ε` is `MaxEnv.shell … cJ ε` (`cg.shellInf_eq`), whose defining conjunct
`cJ - ε ≤ ⟪n_J, z⟫` is a condition on `z` alone.  So a point strictly below that level cannot
be in the shell however it is swept. -/
theorem notMem_shellInf_of_dot_lt (cg : ChainDataGeom ξ xper vl p S gen) {ε : ℕ}
    {z : ℤ × ℤ} (h : Nivat.LE2.dot cg.nJ z < cg.cJ - (ε : ℤ)) :
    z ∉ cg.toChainData.shellInf ε := by
  rw [cg.shellInf_eq ε]
  rintro ⟨g, -, t, rfl, hlev⟩
  exact absurd hlev (not_le.mpr h)

/-- **`exists_case2_window`'s straddle conjunct splits into a level equation and one
membership.**

The conjunct asks, for every `g ∈ 𝒯 ∖ ℓ'_𝒯` and every height `t ≥ τ`, that `t • v_J + g` lie in
`Â_∞^(ε+1)` but not in `Â_∞^(ε)`.  The *second* half is not real work: by
`dot_nJ_vJ_smul_add` the layer of `t • v_J + g` is the layer of `g`, so if the exposed face
sits at the single level `c_J - ε - 1` then `notMem_shellInf_of_dot_lt` rules out `Â_∞^(ε)` at
once, uniformly in `t`.

What remains is `hmem`, the membership in the *next* shell, which is genuine geometry: it needs
the sweep representation of `MaxEnv.shell`, i.e. a point of `Â_∞` carried onto `t • v_J + g` by
non-negatively many `v_{J-1}` steps.  `cg.bottom` at index `ε` is the field that produces
exactly such a `v_J`-half-line at level `c_J - ε - 1`, which is why the level in `hlev` is
pinned to that value and not to an arbitrary one.

⚠ So this lemma is a **reduction, not a proof**: it removes one of the two halves of conjunct
four and leaves the other standing. -/
theorem hface_of_mem_shellInf_succ (cg : ChainDataGeom ξ xper vl p S gen)
    {ε : ℕ} {S₁ Q : Finset (ℤ × ℤ)} {τ : ℤ}
    (hlev : ∀ g ∈ S₁, g ∉ Q → Nivat.LE2.dot cg.nJ g = cg.cJ - (ε : ℤ) - 1)
    (hmem : ∀ g ∈ S₁, g ∉ Q → ∀ t : ℤ, τ ≤ t →
      t • cg.vJ + g ∈ cg.toChainData.shellInf (ε + 1)) :
    ∀ g ∈ S₁, g ∉ Q → ∀ t : ℤ, τ ≤ t →
      t • cg.vJ + g ∈ cg.toChainData.shellInf (ε + 1) ∧
      t • cg.vJ + g ∉ cg.toChainData.shellInf ε := by
  intro g hg hgQ t ht
  refine ⟨hmem g hg hgQ t ht, notMem_shellInf_of_dot_lt cg ?_⟩
  rw [dot_nJ_vJ_smul_add, hlev g hg hgQ]
  omega


/-- **Collé's (4.1) on a generating set: the run above the `n_J`-minimal face.**

`b3_colle2.txt:627` / `:774`.  Given the `n_J`-bottom face of a generating set `W`, there is a
point `q` strictly above that face from which a run of `|bottom face| - 1` consecutive
`v_J`-steps stays inside `W`.

**This is the whole residual content of leaf C as of 2026-09-19.** `exists_case2_window` below
is now *proved* from this statement plus `Claim411.exists_case2_window_maxB_weak_of_run`
(`RegionClaim411.lean:1397`, kernel-clean, `[propext, Classical.choice, Quot.sound]`), which
produces all eleven conjuncts verbatim.  Everything else that used to hide inside C's `sorry`
— the window `𝒯`, the sweep region `R := shiftRegion cg s ε`, the straddle, the `maxB`/
`derivedQ` identification, `hline` — is discharged.

⚠ Per `CLAUDE.md` hard rule 1 this is **a split, not progress**: `sorry TOTAL` is unchanged.
What changed is the *content*: from "place a window and build a region" to one combinatorial
statement about a lattice-convex finite set, with no chain bundle, no shells, and no regions.

Two honest notes on its difficulty:

* It is **trivial when the bottom face has ≤ 1 point** — the run length is then `0`, and any
  `q` above the face works (`hSgen`'s `Nonempty` plus a non-flat `W`).  The content is the
  `≥ 2` case.
* It is the first disjunct of `L1Data.exists_side_with_run_of_latticeConvex`
  (`L1Fields.lean:633`) taken at the side `n := toReal (-n_J)`.  The side is **not** free here:
  the straddle forces the face on the new line to be the `n_J`-minimal one, so the WLOG of
  `b3_colle2.txt:627`/`:774` (Collé's Lemma 2.3 parallelogram) has to be paid, and no lemma in
  the tree currently produces it.  That parallelogram is the shared L1/L3/C bottleneck. -/
theorem exists_case2_run (cg : ChainDataGeom ξ xper vl p S gen)
    {Sgen : Finset (ℤ × ℤ)} (hSgen : Nivat.Colle.IsGeneratingSet ξ Sgen)
    (hvl_prim : Primitive vl) (hdet_vl : det p vl = 0)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_pos : Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0)
    {a₀ : ℤ × ℤ} (ha₀ : a₀ ∈ Sgen)
    (hmin : ∀ w ∈ Sgen, Nivat.LE2.dot cg.nJ a₀ ≤ Nivat.LE2.dot cg.nJ w) :
    ∃ q ∈ Sgen, Nivat.LE2.dot cg.nJ a₀ < Nivat.LE2.dot cg.nJ q ∧
      ∀ i : ℕ, i < (Sgen.filter fun w => Nivat.LE2.dot cg.nJ w = Nivat.LE2.dot cg.nJ a₀).card - 1 →
        q + (i : ℤ) • cg.vJ ∈ Sgen :=
  C11Bridge.exists_run cg hSgen hvl_prim hdet_vl hℓ_nel hℓ_pos hℓ_neg hdet_ℓ ha₀ hmin


/-- **C's one remaining obligation: Claim 4.11's straddling translate `𝒯`, with its line seed.**

`b3_colle2.txt:904` reads *"due to Claim 4.11 and Lemma 4.1, there exists an `(ℓ, ℓ')`-region
`𝒦 ⊂ Â_∞^(ε)` …"*.  Everything on the right of that "due to" is now proved:
`Claim411.claim411_semiAmbiguous` and `Claim411.region_of_claim411_of_sweep`
(`RegionClaim411.lean:243`, `:357`) are both kernel-clean, and `case1_sweep` supplies the
sweep.  What neither supplies is the *left* input — the window placement itself, Collé's
*"`𝒯 ∖ ℓ'_𝒯 ⊂ Â_∞^(ε)` but `𝒯 ⊄ Â_∞^(ε)`"* (`b3_colle2.txt:824`).

This declaration is that placement and nothing else.  `region_periods_and_rays` below is now
**pure assembly**: its body contains no `sorry`, and every hole in it has a name here or in
`case1_sweep`.

## Status, 2026-09-19 (this section is retained, not current — §14)

**`exists_case2_window` is no longer a `sorry`.**  Everything below describes the obligation as
it stood while it was open, and is kept because it records *why* each field has the shape it
has.  Two things in it are now out of date and are corrected here rather than rewritten away:

* `R` is not an unconstrained existential field in the proof that landed — it is
  `Claim411.shiftRegion cg s ε`, a **sub**region of `shellInf ε` whose convexity comes from
  `hRconv` alone.  The reasoning below about why `R` could be neither `Â_∞^(ε)` nor `Â_∞` is
  what forced that choice and is still the right reasoning.
* `hbase` was weakened on 2026-09-19 to `B.Nonempty ∧ ∃ b, ∀ z ∈ S₁, b + z ∈ R`, because no
  consumer in the tree ever destructured both halves at the same `b`.  The strong form's
  companion condition `hheight` went with it.

The residual content moved to `exists_case2_run` (`:2009`) — Collé's (4.1) — and closed when the
`b3_colle2.txt:607` standing hypothesis (`-ℓ, ℓ ∈ nexpd(η)`) was threaded as six binders.

## What has to be produced

A translate `S₁` of the generating window, its `ℓ'`-edge `S₁ ∖ Q` normal to some `n` with
`⟪n, v_J⟫ = 0`, a baseline height `τ`, the Lemma 4.1 seed `(pw, B)`, and the region `R` that
Lemma 4.1 sweeps — such that from height `τ` onwards the window straddles the boundary between
layers: `Q` inside `R ⊆ Â_∞^(ε)`, the edge on the new line `Â_∞^(ε+1) ∖ Â_∞^(ε)`.

## Why `R` is a field and not `Â_∞^(ε)`, and not `Â_∞` either

`case1_sweep`'s `hR_region` asks for `Colle41.IsRegion R p v_J`, whose first conjunct is
`IsLatticeConvexRegion R`.  Neither obvious candidate survives:

* `R := Â_∞^(ε)` is refuted.  `Nivat.ShellConvex.not_forall_isLatticeConvexRegion_shellInf_of_hRconv`
  kernel-refutes `IsLatticeConvexRegion (shellInf ε)` for every `ε`, *including* under
  `hRconv` — the witness `cgc` has `Â_∞` a lattice-convex cone and `shellInf 2` still fails,
  at the midpoint of `(1,-2)` and `(3,0)`.
* `R := Â_∞` is a region (`isRegion_iUnion_Ahat`, kernel-clean above), but it is **too small**.
  `cg.ahat_halfPlane` puts `Â_∞` at levels `⟪n_J, ·⟫ ≥ c_J`, while the whole point of the
  straddle is that `Q` sits one layer *below* that, at level `c_J - ε`.  Demanding
  `t • v_J + Q ⊆ Â_∞` would therefore be a strengthening over Collé's
  *"`𝒯 ∖ ℓ'_𝒯 ⊂ Â_∞^(ε)`"* that the geometry contradicts.  An earlier draft of this
  declaration asked for exactly that and would have been unprovable.

So `R` is existentially quantified, constrained only by `R ⊆ Â_∞^(ε)` and `IsRegion R p v_J`.
Its period `PeriodOn ϑ R (1 • p)` is **not** a field: it follows from `R ⊆ Â_∞^(ε)` and
`Claim411.periodOn_shellInf_p` by `Colle41.PeriodOn.mono`, and the assembly below does that.
Likewise `region_of_claim411_of_sweep`'s own `hQR` (into `Â_∞^(ε)`) is derived from the `R`
form by the containment, so this shape costs the consumer nothing.

⚠ This is a **split, not progress**: `sorry TOTAL` is unchanged, `axiom_closure` is unchanged,
and no step of Claim 4.11's window construction happens here.  What it buys is that leaf C's
obligation is no longer "prove a twelve-binder theorem about regions, rays and periods" but
"place one window", which is a statement the kernel can check on its own and one worker can
own.  Per `CLAUDE.md` hard rule 4 ("拆而后落") the mechanical split goes in before the work is
dispatched.

Hand-read of the intended proof (**not** attempted here, and not to be recorded as done):
`cg.bottom` gives a `v_J`-half-line of `reachSet` at every level below `c_J`, `cg.rec_p` and
`cg.rec_vJ` give the two recession directions, and `hRconv` closes the window up.  Note that
`cg.dot_nJ_vJ` makes the layer index **invariant** under `t • v_J`, so the straddle, once
achieved at one height, holds at every `t ≥ τ` — that is why `τ` is a single number and not a
function of the window.  For `R` itself the natural candidate is the forward `p`-closure of the
swept half-strip: `⟪n_J, p⟫ > 0` (`Claim411.dot_nJ_p_pos`) keeps it above level `c_J - ε`, and
`Claim411.add_p_mem_shellInf_self` keeps it inside `Â_∞^(ε)`. -/
theorem exists_case2_window (cg : ChainDataGeom ξ xper vl p S gen)
    (hξ : IsMinimalCounterexample ξ)
    (hSφ : Nivat.Colle.IsGeneratingSet ξ S)
    (hϑ_mem : ϑ ∈ orbitClosure ξ)
    (hRconv : IsLatticeConvexRegion (⋃ i, cg.toChainData.Ahat i))
    (hRne : (⋃ i, cg.toChainData.Ahat i).Nonempty)
    -- **Lemma 2.4's `𝒮` and its deficit, threaded 2026-09-19.**  `Sgen` is *not* `cg.S`
    -- (`:1848`): `S` is `𝒮_φ`, `Sgen` is the bi-oriented generating set `exists_preamble`
    -- produces.  Both were already binders of `region_periods_and_rays` (`:2044`, `:2073`) and
    -- in scope at its call of this theorem (`:2091`), which simply did not pass them.  Adding
    -- them here is free at the call site and strictly **weakens** this obligation — Claim 4.11's
    -- producer (`RegionClaim411.exists_case2_window_of_run_of_height`, `:1209`) needs Claim 4.2's
    -- ∀-form to build the window at all, so without these the `sorry` was harder than the
    -- mathematics it stands for.
    {Sgen : Finset (ℤ × ℤ)} (hSgen : Nivat.Colle.IsGeneratingSet ξ Sgen)
    (hdef : ∀ (n : ℝ × ℝ) (cmax cmin : ℝ),
      (∀ z ∈ Sgen, inner2 n z ≤ cmax) → (Nivat.R2.face Sgen n cmax).Nonempty →
      (∀ z ∈ Sgen, cmin ≤ inner2 n z) → (Nivat.R2.face Sgen n cmin).Nonempty →
        P ξ Sgen - P ξ (Sgen.filter fun z => inner2 n z < cmax) ≤
          (Nivat.R2.face Sgen n cmax).card - 1 ∧
        P ξ Sgen - P ξ (Sgen.filter fun z => cmin < inner2 n z) ≤
          (Nivat.R2.face Sgen n cmin).card - 1)
    {K ε : ℕ}
    (hshell_ε : ∀ z ∈ cg.toChainData.shellInf ε, ϑ z = T ((K : ℤ) • vl) xper z)
    (hshell_not_εp1 :
      ¬ (∀ z ∈ cg.toChainData.shellInf (ε + 1), ϑ z = T ((K : ℤ) • vl) xper z))
    -- **Lemma 2.3's bi-oriented direction, threaded 2026-09-19.**  Collé's (4.1)
    -- (`b3_colle2.txt:627`) does not come from lattice-convexity of `Sgen` alone — it comes
    -- from *both* `ℓ` and `-ℓ` lying in `nexpd(η)`, which is a standing hypothesis of his
    -- Lemma 4.1 (`:607`) and which this signature simply did not carry:
    --   "Since `-ℓ, ℓ ∈ nexpd(η)`, from Lemma 2.3 we get that `𝒮` has an edge parallel to `ℓ`
    --    and another one parallel to `-ℓ`."
    -- Without `hℓ_neg` the run of (4.1) has length `0` and `exists_case2_run` below is not
    -- provable — the missing-binder failure mode of `PROTOCOL.md` §15, found by lane L3band
    -- on 2026-09-19 and confirmed against the paper before the binders were added.
    -- **All six are free at the call site**: `ColleRegion.lean:356` obtains `hℓ_nel/hℓ_pos/
    -- hℓ_neg` from `exists_biONED_direction` and `:363` obtains `hvl_prim/hdet_vl/hdet_ℓ`
    -- from `exists_preamble`, both *before* the Case 1 / Case 2 split, so neither branch pays
    -- anything for them.  Adding them strictly **weakens** this obligation.
    (hvl_prim : Primitive vl) (hdet_vl : det p vl = 0)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_pos : Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0) :
    ∃ (S₁ Q B : Finset (ℤ × ℤ)) (τ : ℤ) (pw : ℕ) (R : Set (ℤ × ℤ)),
      -- `𝒯` is still a generating window.
      Nivat.Colle.IsGeneratingSet ξ S₁ ∧
      Q ⊆ S₁ ∧
      -- `S₁ ∖ Q` is the face normal to `n`, and `n ⟂ v_J` makes it an `ℓ'`-edge.
      (∃ (n : ℝ × ℝ) (cmax : ℝ),
        n ≠ 0 ∧
        inner2 n cg.vJ = 0 ∧
        (∀ z ∈ S₁, inner2 n z ≤ cmax) ∧
        (Nivat.R2.face S₁ n cmax).Nonempty ∧
        Q = S₁.filter fun z => inner2 n z < cmax) ∧
      -- The edge sits on the new line, at every height `t ≥ τ`.
      (∀ g ∈ S₁, g ∉ Q → ∀ t : ℤ, τ ≤ t →
        t • cg.vJ + g ∈ cg.toChainData.shellInf (ε + 1) ∧
        t • cg.vJ + g ∉ cg.toChainData.shellInf ε) ∧
      -- Claim 4.2's deficit for `𝒯`, and Lemma 4.1's line seed.
      P ξ S₁ ≤ P ξ Q + pw ∧
      (∀ g ∈ B, ∀ i : ℕ, i < pw → g + (i : ℤ) • cg.vJ ∈ Q) ∧
      -- The swept region: inside layer `ε`, and a genuine `(ℓ, ℓ')`-region.
      R ⊆ cg.toChainData.shellInf ε ∧
      Colle41.IsRegion R p cg.vJ ∧
      -- `case1_sweep`'s `hQR`: the swept window, and its `+p` translate, stay in `R`.
      (∀ t : ℤ, τ ≤ t → ∀ z ∈ Q,
        t • cg.vJ + z ∈ R ∧ t • cg.vJ + z + (1 : ℤ) • p ∈ R) ∧
      -- `case1_sweep`'s `hB_covers_window`, **weakened 2026-09-19** from `∃ b ∈ B, …`.  See the
      -- binder's own note at `case1_seed`: the two halves are consumed separately downstream,
      -- and the strong form charged leaf C an absolute window-height condition on `Sgen` that
      -- Lemma 2.4 cannot deliver.
      (B.Nonempty ∧ ∃ b, ∀ z ∈ S₁, b + z ∈ R) ∧
      -- **`case1_sweep`'s `hBmax`, added 2026-09-19.**  ⚠ This is a **genuine new obligation on
      -- leaf C**, not bookkeeping.  It arrived because `case1_sweep` grew this binder in order
      -- to close `case1_seed`, and C is its second call site (`:2083`).
      --
      -- It does not make C's `hsweep` more expensive *relative to what C was always going to
      -- owe*.  C's sweep is free today only because `case1_sweep`'s body is `sorry`, and a
      -- `sorry` body supplies any binder list at all; once the seed closes, C has to meet
      -- `case1_sweep`'s real hypotheses like everyone else.  Better to see the bill now.
      --
      -- **Why it is the canonical choice rather than an arbitrary pin**, which is the part that
      -- decides whether C can pay it:
      -- * `maxB Q u' pw = Q.filter (fun g => ∀ i < pw, g + i • u' ∈ Q)` (`L1Cut.lean:116`) is
      --   *by definition* the largest set satisfying the `hline` conjunct three lines above.
      --   Taking `B` maximal makes `hline` hold by construction (`maxB_hBQ`) and makes
      --   `hB_covers_window` **easier**, since that conjunct is existential in `b ∈ B` and `B`
      --   only grows.  Both move in C's favour.
      -- * `derivedQ ε u' S₁` is `S₁` cut at the `u'`-parallel top edge (`L1Cut.lean:98`) —
      --   which is what the `hQ_edge` conjunct above already forces `Q` to be, up to the sign
      --   of the normal; the `ε : Bool` is exactly that sign.
      -- * `pw = (topFace ε u' S₁).card - 1` is the width Lemma 2.4's boundary deficit
      --   delivers (`hdef`), so it is the value `P ξ S₁ ≤ P ξ Q + pw` is meant to be read at.
      --
      -- ⚠ **Unverified consequence, flagged not hidden:** `Case2WindowProbe`'s `cgg` model
      -- satisfies the previous ten conjuncts at `ε = 0`; whether it satisfies this eleventh is
      -- **not** measured. If it does not, that is evidence against this conjunct, not against
      -- the model. Re-checking it is dispatched, not assumed.
      (∃ e : Bool, pw = (L1Data.topFace e cg.vJ S₁).card - 1 ∧
        B = L1Data.maxB (L1Data.derivedQ e cg.vJ S₁) cg.vJ pw) := by
  -- **Wired 2026-09-19.**  No longer a `sorry`: Claim 4.11's producer supplies all eleven
  -- conjuncts verbatim, and the only thing it asks for beyond this theorem's own binders is
  -- the `n_J`-minimal point (free) and Collé's (4.1) run (`exists_case2_run`, above).
  obtain ⟨a₀, ha₀, hmin⟩ := Sgen.exists_min_image (fun w => Nivat.LE2.dot cg.nJ w) hSgen.1
  obtain ⟨q, hqW, hqgt, hrun⟩ :=
    exists_case2_run cg hSgen hvl_prim hdet_vl hℓ_nel hℓ_pos hℓ_neg hdet_ℓ ha₀ hmin
  exact Claim411.exists_case2_window_maxB_weak_of_run cg hRconv hSgen
    (L1Data.isGeneratingSet_image hSgen) hdef ε ha₀ hmin hqW hqgt hrun

/-- Two independent periods of `ϑ` on a **sub**region `R ⊆ Â_∞`, together with base points
whose forward rays stay inside `R`.

This is the merge of the original `h_two_periods` and `h_base_points` steps; see joint 2 in
the module docstring for why they cannot be separated.

## Scope corrected 2026-09-17 — the periods do not hold on all of `Â_∞`

The previous form concluded both periods on `⋃ i, cg.Ahat i` and derived the second from
`DoublyPeriodic xper`.  Both halves were wrong, and the fix is one and the same.  Collé's
Claim 4.11 opens (`b3_colle2.txt:900`)

> let `h ∈ ℤ²` denote a period for `ϑ|Â_∞^{(ε)}` **parallel to `−ℓ`**

— one period on the shell, not two — and produces the second only after shrinking
(`b3_colle2.txt:904`)

> Due to Claim 4.11 and Lemma 4.1, there exists an `(ℓ,ℓ')`-region `𝒦 ⊂ Â_∞^{(ε)}` such that
> `ϑ|𝒦` is fully periodic with a period parallel to `ℓ` and another one parallel to `ℓ'`.

`ColleRegion.colle_region` only ever asks for *some* region (`∃ R`), so handing it `𝒦`
instead of `Â_∞` costs nothing downstream.  The ambient `Â_∞` enters as the hypotheses
`hRconv`/`hRne` — it is Lemma 4.1's ambient region `R`, which is why
`region_latticeConvex` and `region_nonempty` stay live in the assembly.

## `Sgen` is Lemma 2.4's `𝒮`, not `cg.S` (2026-09-17)

Claim 4.11 is stated over translates of Lemma 2.4's generating set (`b3_colle2.txt:900`):

> `ϑ` is an `(ℓ', 𝒯, +)`-semi-ambiguous configuration for any translation `𝒯` of `𝒮` where
> `𝒯 \ ℓ'_𝒯 ⊂ Â_∞^{(ε)}`, but `𝒯 ⊄ Â_∞^{(ε)}`.

That `𝒮` is fixed at the top of the proof of Lemma 4.5 (`:774`, *"Let `𝒮 ⊂ ℤ²`, with
`𝒮 ∩ ℓ_𝒮` contained in `ℓ^(−)`, be an `η`-generating set as in Lemma 2.4"*) and is the `S` of
`exists_preamble`.  The chain, on the other hand, is indexed by `𝒮_φ` (Lemma 3.5, `:424-428`;
Case 2, `:758`) — in the assembly `cg.S = d.Sphi`.  Collé never identifies the two sets, and
binding them as one variable would make this theorem demand Lemma 2.4's data about the
zonotope `𝒮_φ`, which nothing in the tree produces (the same conflation the deleted
`decomp.Sphi = S` field used to assert by fiat).  So Lemma 2.4's set enters through its own
binder `Sgen` with `hSgen : IsGeneratingSet ξ Sgen`; the assembly passes `exists_preamble`'s
`hSgen`, **not** `d.isGeneratingSet` (which is about `𝒮_φ`).  The deficit bound `hdef` for the
same set is not taken yet; it is in scope at the call site when it is needed.

## Route, and what is missing

`Nivat.Colle41.lemma41_colle_region_shape` (`Lemma41.lean:767`, `sorry`-free) has exactly
the conclusion below, and `Nivat.Colle41.lemma41_of_sweep` proves it from a
`Nivat.Colle41.SweepData`.  What is missing is the *construction* of that bundle from `cg`
and `hagree`, i.e. Claim 4.11 — `Claim43.lean:123` records that the sweep construction is
absent, and `:148` that an earlier `exists_sweepData` was withdrawn as false.  That is this
step's remaining content.

## Why the r67 refutation no longer applies

`Nivat.ColleStep.not_region_periods_and_rays` (`Step_PeriodsRays.lean:556`) refutes the
*bare-`ChainData`* form of this statement, kernel-clean, and the fix in 2026-09-16 was to
restore `hξ`.  That is no longer the discriminating hypothesis, and `hξ` is gone.  What the
witness fails now is `ChainDataGeom` itself: its region is the half-strip
`Â_∞ = [0,∞) × [0,1]` (`cxShellInf`/`cxB`, `Step_PeriodsRays.lean:141-147`), whose recession
set is `{(m,0) : 0 ≤ m}` — one direction only.

⚠ **Corrected 2026-09-18.**  This paragraph used to say the witness fails `rec_p` alone,
citing `ChainGeom.lean:102` and the fact that `p ∥ vl = (0,1)`.  Both halves were wrong.
`rec_p` is `ChainGeom.lean:109` (`:102` is inside `bottom`).  And `p ∥ vl` was forced by
`hdet_vl : det p vl = 0` (`Step_PeriodsRays.lean:34`), a hypothesis the *current* statement
does not carry: `p` is a free parameter here, so one may take `p := (1,0)`, and then `rec_p`
holds on the half-strip and `hp_per : (1,0) ∈ Per cxXper` holds too — `cxXper` is the zero
configuration (`Step_PeriodsRays.lean:126`), whose period group is all of `ℤ²`.

The escape that is actually real is the **conjunction** `rec_p` (`ChainGeom.lean:109`) +
`rec_vJ` (`:117`) + `vJ_ne` (`:113`) + `dot_nJ_vJ` (`:95`) + `dot_nJ_p` (`:111`): those five
make `p` and `vJ` independent by `det_ne_zero_of_dot` (`ChainGeom.lean:250`), while both must
be recession directions of `Â_∞`.  A set receding in two independent directions is not a
half-strip.  So the refutation still says nothing about the form below — but for that reason,
not the one previously given here.

`hξ` was dropped rather than kept because it is now unused: none of `rec_p`, `rec_vJ`,
`vJ_ne`, `dot_nJ_vJ`, `dot_nJ_p` or `hagree` needs minimality.  Its content has moved into
the constructor, which is where Collé §3 supplies it.

## The `h' = n • cg.vJ` clause (added 2026-09-18, before any proof body existed)

The last clause pins `h'` to a **positive** multiple of `cg.vJ`.  It is not new mathematics
and it is not a guess: both known producers of this conclusion build `h'` that way and then
discard the information by existential quantification.

* `Nivat.Colle41.lemma41_of_sweep` (`Lemma41.lean:723`) `refine`s with
  `h' := ((t₀ * q : ℕ) : ℤ) • u'`, positive by `:729` (`Nat.mul_pos ht₀ hq`), and `u'` is the
  `v_{ℓ'}` of Lemma 4.1.  This is the route named above.
* The retired `region_periods_and_rays_of_geom` (`ChainGeom.lean:228`) independently builds
  `(N.natAbs : ℤ) • cg.vJ` with `N ≠ 0`.

The consumer that needs it is `Claim414.claim414_ellprime` (`Claim414EllPrime.lean:160`),
whose `hrayv` is a ray along `cg.vJ` itself and whose `hh'_par`/`hh'_ne` are exactly
`det h' cg.vJ = 0` and `h' ≠ 0`; `ColleReg.rayIn_of_rayIn_nsmul` (`RegionTranslate.lean:145`)
converts the coarse ray into the fine one, and needs the positivity — for a negative
multiple the hypothesis describes the `-cg.vJ` ray and the conversion is false.  Aligning
here rather than after the `sorry` is deliberate: the proof body does not exist yet, so the
alignment costs nothing now and a full re-proof later.

## Refuted again, and repaired, 2026-09-18 — `Step_PeriodsRays2.lean`

The sentence "`hξ` was dropped rather than kept because it is now unused" (end of "Why the
r67 refutation no longer applies") was wrong, and the way it was wrong is the one CLAUDE.md
warns about: "unused" was judged against a `sorry` body, which is exactly when the linter is
blind.
`Nivat.ColleStep.PeriodsRays2.not_RPRStatement` refutes the 2026-09-17 form kernel-clean
(`[propext, Classical.choice, Quot.sound]`, measured 2026-09-18) with a witness that **does**
carry a `ChainDataGeom`, every field proved: `Â_∞` is the closed first quadrant (receding in
both `p = (0,1)` and `v_J = (1,0)`), `xper z = z.1`, `ϑ z = z.1`, `ξ z = z.1 + [z.2 < 0]`.
The conclusion demands `ϑ (z + n•v_J) = ϑ z` with `n > 0`, i.e. `z.1 + n = z.1`.

What the witness exploits is that the second period has no source.  Collé's source is
`b3_colle2.txt:904`, *"Due to Claim 4.11 **and Lemma 4.1**"*, and the Lean Lemma 4.1,
`Colle41.lemma41_of_sweep` (`Lemma41.lean:702-703`), takes `(Set.range η).Finite` and
`x ∈ orbitClosure η` as its first two arguments.  Neither was in the signature: `ξ` could have
infinite range and `ϑ` was a free parameter.  Both are bound at the call site
(`ColleRegion.lean:354` `hfin := hξ.1.1`, `:378` `hϑ_mem`), so restoring them is within the
file contract.

Consumption plan (签名落地协议 step 2), written before any proof body exists:

* `hξ` → `hξ.1.1` is `lemma41_of_sweep`'s `hfinη`; the rest of `hξ` feeds Claim 4.11's
  complexity bound `hdef : P η S ≤ P η Q + p` (`Lemma41.lean:706`), which is where minimality
  enters Collé's `:896-904`.
* `hϑ_mem` → `lemma41_of_sweep`'s `hx`.

`hϑ_periodic` is *not* added: `PeriodOn ϑ Â_∞ p` follows from `hagree`, `hp_per` and
`cg.rec_p`, so it would be decoration.  With `hξ` back this is an `hξ`-proposition; per
CLAUDE.md 「`IsMinimalCounterexample` 的两层含义」 no further falsification is to be
dispatched at it, and the proof has to be done honestly.

### Two further locks, same day

The witness above also sets `Env := fun _ => True` and `cg.S := {0}`, both legal because the
statement constrained neither.  Neither is what Collé works with, and both are already bound
at the call site, so both are now taken, copying `region_not_periodic`'s binders verbatim
(`:1401-1402`):

* `hc_env` — `ChainData.Env` is deliberately abstract (`Lemma35.lean:698`); without this the
  chain's sets need not be `E(𝒮_φ)`-enveloped at all, and Def 3.2 envelopedness is what makes
  `Â_∞` a region in Collé's sense (`b3_colle2.txt:402`).  Produced by `exists_chainData`
  (`ColleRegion.lean:371`).
* `hgen` — without it `cg.S` may be a single point, which makes `lex`, `lex'`, `edge`, `edge'`
  (`ChainGeom.lean:83-93`) vacuous and the window degenerate.  Collé's `𝒮_φ = conv(-supp φ) ∩ ℤ²`
  (`b3_colle2.txt:298`) is a singleton only for a monomial annihilator, which is excluded.
  Consumed through Claim 4.11's complexity bound `hdef : P η S ≤ P η Q + p`
  (`Lemma41.lean:706`), which is a statement *about this `S`* and is vacuous content unless
  `S` is the generating window.

Both are locks against the next witness rather than against this one — `hξ` alone already
kills `Step_PeriodsRays2`'s.  They are recorded as such, not claimed as proof progress.

## (4.6) and the deficit restored, 2026-09-18 — the signature could not reconstruct Claim 4.11

Collé's Claim 4.11 (`b3_colle2.txt:900`) is proved at `:902`, verbatim:

> Indeed, let `h ∈ ℤ²` denote a period for `ϑ|Â_∞^(ε)` parallel to `−ℓ`.  Since, **due to
> (4.6)**, `ϑ|Â_∞^(ε+1)` is not periodic of period `h`, the proof is identical to that one of
> Claim 4.7.

and (4.6) is `:894`: `ϑ|Â_∞^(ε) = x̂_per|Â_∞^(ε)` **but** `ϑ|Â_∞^(ε+1) ≠ x̂_per|Â_∞^(ε+1)`.

Line up the two claims.  `case1_claim47_semiAmbiguous` (Claim 4.7, proved 2026-09-18) runs on
the pair `hRper : PeriodOn ξ' R (c•u)` together with `hnonper_R' : ¬ PeriodOn ξ' R' (c•u)` for
a strictly larger `R'`; that pair is what makes the ray-upgrade contradict maximality.  Claim
4.11's corresponding pair is `R := Â_∞^(ε)`, `R' := Â_∞^(ε+1)`, and **(4.6) is the sole source
of its second half**.  The signature had no `ε` and no shell facts at all, so it could not
state, let alone prove, "not periodic on the next shell".  The `sorry` hid this: per CLAUDE.md
「`sorry` 会关掉『假设没被用上』这条诊断信号」, a missing hypothesis is invisible until a body
exists, which is exactly why this is being fixed before one does.

Within the file contract: all three are already bound at the call site
(`ColleRegion.lean:378`, from `Colle35.lemma35`, whose conclusion `Lemma35.lean:882-884` is
`∃ ε : ℕ, (∀ z ∈ c.shellInf ε, …) ∧ ¬ (∀ z ∈ c.shellInf (ε+1), …)`), and `hshell_ε` /
`hshell_not_εp1` are the same two binders `region_not_periodic` already takes at
`ColleRegion.lean:405`.

`hdef` likewise: it is `lemma41_of_sweep`'s `hdef : P η S ≤ P η Q + p` (`Lemma41.lean:706`),
i.e. Claim 4.2's complexity deficit, without which the Lemma 4.1 endgame at `:904` cannot be
invoked at all.  `ColleRegion.lean:360-361` already anticipated this in so many words —
*"`hdef` goes to Case 1 and, once `region_periods_and_rays` takes it, to Claim 4.11 too"*.

Consumption plan (签名落地协议 step 2), written before any proof body exists:

* `hshell_ε` → the `R := Â_∞^(ε)` half of Claim 4.11's period pair: with `hagree` it pins `ϑ`
  to `x̂_per` on the shell, so `hp_per` transports to a period of `ϑ` there.
* `hshell_not_εp1` → the `¬ PeriodOn` half, i.e. `case1_claim47_semiAmbiguous`'s
  `hnonper_R'` slot.  This is the one the signature was missing outright.
* `hdef` → `Colle41.lemma41_of_sweep`'s `hdef` (`Lemma41.lean:706`), through Claim 4.2.

`hϑ_periodic` (`Colle35.lemma35`'s `PeriodicOnWith ϑ (⋃ i, c.Ahat i) p`) is deliberately
**not** added even though it too is in scope at `:378`: it is derivable here from `hagree`,
`hp_per` and `cg.rec_p`, so taking it would be decoration.  That judgement is unchanged from
the 2026-09-18 entry above; only the three genuinely underivable facts are restored.

## 2026-09-19: the conclusion's containment was `⋃ i, Ahat i`, and was **stronger than Collé**

`b3_colle2.txt:904` says *"there exists an `(ℓ, ℓ')`-region `𝒦 ⊂ Â_∞^(ε)`"* — the shell at
level `ε`, not `Â_∞`.  Our `⋃ i, cg.toChainData.Ahat i` form was not merely different but
strictly stronger and **unreachable**: `shellInfZero` (`Lemma35.lean:741`) gives only
`shellInf 0 ⊆ ⋃ i, Ahat i`, and the shells grow with `ε`, so nothing transports a region
from level `ε` down to `Â_∞`.

It was also **dead**.  The sole consumer, `ColleRegion.lean:399-402`, destructures the
containment as `-`:

    obtain ⟨R, -, hRconv', hRne', h, h', z₀, z₀', hdet, hray_h, hray_h', hper_h, hper_h',
      n, hn, hh'_eq⟩ := region_periods_and_rays cg hSgen hξ hϑ_mem hc_env hgenφ hc_grow hp_mem …

`claim414_of_chainDataGeom` takes the separate binder `hR_lattice_convex` (about `⋃ Ahat`)
and never the containment.  So the change below is a pure weakening at zero downstream cost,
and it makes the conclusion match `Claim411.region_of_claim411_of_sweep`
(`RegionClaim411.lean:357`) exactly.

⚠ This does **not** revive `Step_PeriodsRays2.lean`'s refutation.  That file refutes
`RPRStatement`, a verbatim *copy* of the 2026-09-17 signature with binders made explicit, and
its bridging `example` is deliberately not kept live — the repaired signature takes `hξ` and
`hϑ_mem`, which `RPRStatement` does not offer.  Weakening the conclusion cannot re-establish
that bridge; it would only make the copy harder to refute, not the theorem easier to state. -/
theorem region_periods_and_rays (cg : ChainDataGeom ξ xper vl p S gen)
    {Sgen : Finset (ℤ × ℤ)} (hSgen : Nivat.Colle.IsGeneratingSet ξ Sgen)
    -- **`S_φ` itself generates** (2026-09-19).  `Claim411.claim411_semiAmbiguous`
    -- (`RegionClaim411.lean:243`) consumes it for the Figure 11(B) ray upgrade, and it is
    -- **not** derivable from the binders already here.  Unfolding `Generating.lean:58-60`,
    --   `IsGeneratingSet ξ S = S.Nonempty ∧ LatticeConvex S ∧
    --                          ∀ a ∈ S, LatticeConvex (S.erase a) → GeneratesAt ξ S a`
    -- so it is strictly stronger than the `hgen : GeneratesAt ξ S gen` below in three
    -- separate ways: nonemptiness, lattice-convexity of `S`, and *every* site rather than
    -- the single site `gen`.  None of the three follows from `hgen`.
    -- Free at the call site: `ColleRegion.lean:408` already hands `d.isGeneratingSet`
    -- (`DecompData.lean:195`, `IsGeneratingSet η D.Sphi`) to `region_not_periodic`, and `cg`
    -- there is instantiated at `S := d.Sphi`.
    (hSφ : Nivat.Colle.IsGeneratingSet ξ S)
    {K : ℕ}
    (hξ : IsMinimalCounterexample ξ)
    (hϑ_mem : ϑ ∈ orbitClosure ξ)
    (hc_env : cg.toChainData.Env = Nivat.LE2.EnvOf (S : Set (ℤ × ℤ)))
    (hgen : Nivat.Colle.GeneratesAt ξ S gen)
    -- **Weakened 2026-09-20.**  Was `∀ i, cg.toChainData.B i ⊂ cg.toChainData.B (i + 1)`.
    -- That binder is not used in this theorem's body at all, and its only use one level
    -- down (`ChainGeom.lean:347`) was `region_nonempty`, which needs nothing beyond an
    -- inhabited `B 1`.  See `Step_Nonempty.lean`.
    (hB1 : (cg.toChainData.B 1).Nonempty)
    (hp_per : p ∈ Per xper)
    (hRconv : IsLatticeConvexRegion (⋃ i, cg.toChainData.Ahat i))
    (hRne : (⋃ i, cg.toChainData.Ahat i).Nonempty)
    (hagree : ∀ z ∈ ⋃ i, cg.toChainData.Ahat i, ϑ z = T ((K : ℤ) • vl) xper z)
    -- (4.6), `b3_colle2.txt:894`, the input Claim 4.11's proof names explicitly at `:902`.
    {ε : ℕ}
    (hshell_ε : ∀ z ∈ cg.toChainData.shellInf ε, ϑ z = T ((K : ℤ) • vl) xper z)
    (hshell_not_εp1 :
      ¬ (∀ z ∈ cg.toChainData.shellInf (ε + 1), ϑ z = T ((K : ℤ) • vl) xper z))
    -- Claim 4.2's deficit, `lemma41_of_sweep`'s `hdef` (`Lemma41.lean:706`).
    (hdef : ∀ (n : ℝ × ℝ) (cmax cmin : ℝ),
      (∀ z ∈ Sgen, inner2 n z ≤ cmax) → (Nivat.R2.face Sgen n cmax).Nonempty →
      (∀ z ∈ Sgen, cmin ≤ inner2 n z) → (Nivat.R2.face Sgen n cmin).Nonempty →
        P ξ Sgen - P ξ (Sgen.filter fun z => inner2 n z < cmax) ≤
          (Nivat.R2.face Sgen n cmax).card - 1 ∧
        P ξ Sgen - P ξ (Sgen.filter fun z => cmin < inner2 n z) ≤
          (Nivat.R2.face Sgen n cmin).card - 1)
    -- Lemma 2.3's bi-oriented direction, passed straight through to `exists_case2_window`
    -- (`:1806`); see the note there.  All six are already in scope at this theorem's own call
    -- site (`ColleRegion.lean:401`), obtained before the case split.
    (hvl_prim : Primitive vl) (hdet_vl : det p vl = 0)
    (hℓ_nel : ℓ ∈ Colle45.NonExpansiveLine ξ)
    (hℓ_pos : Colle45.IsOneSidedNonexpansive ξ ℓ)
    (hℓ_neg : Colle45.IsOneSidedNonexpansive ξ (-ℓ))
    (hdet_ℓ : Nivat.LE2.dot ℓ vl = 0) :
    ∃ R : Set (ℤ × ℤ), R ⊆ cg.toChainData.shellInf ε ∧
      IsLatticeConvexRegion R ∧ R.Nonempty ∧
      ∃ h h' z₀ z₀' : ℤ × ℤ, det h h' ≠ 0 ∧
        (∀ k : ℕ, z₀ + (k : ℤ) • h ∈ R) ∧
        (∀ k : ℕ, z₀' + (k : ℤ) • h' ∈ R) ∧
        (∀ z ∈ R, z + h ∈ R → ϑ (z + h) = ϑ z) ∧
        (∀ z ∈ R, z + h' ∈ R → ϑ (z + h') = ϑ z) ∧
        ∃ n : ℕ, 0 < n ∧ h' = (n : ℤ) • cg.vJ := by
  classical
  obtain ⟨S₁, Q, B, τ, pw, R, hS₁, hQS, hQ_edge, hface, hdef41, hline, hRsub, hR_region,
    hQR_R, hbase, hBmax⟩ :=
    exists_case2_window cg hξ hSφ hϑ_mem hRconv hRne hSgen hdef hshell_ε hshell_not_εp1
      hvl_prim hdet_vl hℓ_nel hℓ_pos hℓ_neg hdet_ℓ
  have hQR : ∀ t : ℤ, τ ≤ t → ∀ z ∈ Q, t • cg.vJ + z ∈ cg.toChainData.shellInf ε :=
    fun t ht z hz => hRsub (hQR_R t ht z hz).1
  have hdet : det p cg.vJ ≠ 0 := det_ne_zero_of_dot cg.vJ_ne cg.dot_nJ_vJ cg.dot_nJ_p
  have hRper : Colle41.PeriodOn ϑ R ((1 : ℤ) • p) := by
    rw [one_smul]
    exact Colle41.PeriodOn.mono hRsub (Claim411.periodOn_shellInf_p cg hp_per hshell_ε)
  have hamb : Colle41.SemiAmbiguousAlong ξ ϑ S₁ Q cg.vJ τ :=
    Claim411.claim411_semiAmbiguous cg hSφ hϑ_mem hp_per hshell_ε hshell_not_εp1
      hS₁ hQS hQ_edge hQR hface
  -- `case1_sweep` has a `sorry` body, so *applying* it adds no `sorry`: `hsweep` is free.
  have hsweep : ∀ q : ℕ, 0 < q →
      (∀ g ∈ B, ∀ t : ℤ, τ + (pw : ℤ) ≤ t →
        ϑ (g + (t + (q : ℤ)) • cg.vJ) = ϑ (g + t • cg.vJ)) →
      ∃ Kset : Set (ℤ × ℤ), Kset ⊆ cg.toChainData.shellInf ε ∧
        Colle41.IsRegion Kset p cg.vJ ∧ Kset.Nonempty ∧
        ∃ t₀ : ℕ, 0 < t₀ ∧ Colle41.PeriodOn ϑ Kset (((t₀ * q : ℕ) : ℤ) • cg.vJ) := by
    intro q hq hper
    obtain ⟨Kset, hKR, hKreg, hKne, t₀, ht₀, hperK⟩ :=
      case1_sweep (S := S₁) hξ hS₁ hϑ_mem hQS hdet one_ne_zero cg.vJ_prim hdef41 hline
        hRper hR_region hQR_R hbase hamb hBmax q hq hper
    exact ⟨Kset, hKR.trans hRsub, hKreg, hKne, t₀, ht₀, hperK⟩
  exact Claim411.region_of_claim411_of_sweep cg hξ.1.1 hSφ hϑ_mem hp_per hshell_ε
    hshell_not_εp1 hS₁ hQS hQ_edge hQR hface hdef41 hline hsweep

/-- The configuration `ϑ` produced by Lemma 3.5 is not periodic.

`hshell_not` says `ϑ` differs from `x̂_per = T (K • vl) xper` somewhere on the shell
`Â_∞^{(ε+1)}`, while `hagree` and `hshell` say they agree on `Â_∞` and on `Â_∞^{(ε)}`.

The inline version of this step asserted in a comment that non-periodicity "follows from"
the shell mismatch.  That implication is not obvious and has not been checked: a mismatch
with one fully periodic configuration does not by itself make `ϑ` aperiodic.  In the source,
aperiodicity comes from the maximality of `Â_i` (`c.maximalHat`), which is therefore
available via `c`.

## `hξ` restored 2026-09-16 (r67 verdict)

Without `hξ` this statement is **false**: `Nivat.ColleStep.region_not_periodic_refuted_strong`
(`Step_NotPeriodic.lean:430`) refutes it, kernel-clean, and survives re-adding
`xper ∈ orbitClosure ξ`, `¬ IsPeriodic ξ` and `hc_grow`.  It does **not** survive `hξ`: its
witness `ξ = fun z => [0 ≤ z.1] + [0 ≤ z.2]` has `ξ (-1,-1) = 0`, failing the positivity
clause of `IsCounterexample` (`Section8/ExternalDefs.lean:49`).  That file's claim that the
statement "stays false under every natural repair" was measured only against the three
hypotheses above, not against `hξ`.

This does **not** make the theorem true.  `Step_NotPeriodic.lean` also observes that
`¬ IsPeriodic ϑ` (one nonzero period) is strictly stronger than the "no fully periodic
accumulation point" that Colle's Claim 3.7 delivers; whether `hξ` closes that gap is open.

## Conclusion weakened 2026-09-16 (FROZEN E1, `blueprint/FROZEN.md:93-96`)

The conclusion below is now Claim 3.7's, not `¬ IsPeriodic ϑ`.  `FROZEN.md:95-96` records
this as forced rather than optional: the stronger conclusion is refuted in the tree.

**This left the alias discipline (`FROZEN.md:100-101`) failing, and it still is.**
Measured, not inferred — `tmp/subst_check.lean` performs the substitution at the marked
call site `Nivat.exists_fullyPeriodic_region'`（`Section8/ExternalDischarged.lean:75`——旧引 `:89` 越界，
该文件共 79 行；2026-09-25 集成者订正）and `bash scripts/check1.sh` reports:

    tmp/subst_check.lean:33:19: error: Application type mismatch: The argument
      hξ'np
    has type
      ℤ × ℤ
    of sort `Type` but is expected to have type
      ¬IsPeriodic ξ'
    EXIT=1

`ColleRegion.lean:256-258` now exports the weak clause, while the axiom
`Nivat.colle_region`（🔴 **该公理已于 2026-09-18 删除**，见 `Section8/External.lean:652-653`；旧引
External.lean 的 `:697` 越界，该文件今共 666 行（⚠ 同 `:1384`，此处故意不写全 `文件名.lean:行号` 形，
理由见 PROTOCOL §107）。⚠ 因此本段「**the axiom** … still exports」的**主语**
和行号一起腐烂了：今天 `ExternalDischarged.lean:75` 调的是**定理** `Nivat.ColleReg.colle_region`。
⚠ 本次只订正被引对象与行号，**「别名纪律是否仍失败」未重测**——那需要重跑 `tmp/subst_check.lean`，
`:5330` 的「and it still is」按 §15 现降为「读法，非内核事实」。2026-09-25 集成者）exported `¬ IsPeriodic ξ'`, which
`FirstHalfPlane.lean` consumes four times — at `:1352`
(`IsMinimalCounterexample.of_mem_orbitClosure`), `:1365` (`exists_modP_decomp`), `:1376`
(`isPeriodic_modP_iff`), and in that theorem's own conclusion at `:1341`.

So closing the `sorry`s in this file is **not** sufficient to discharge the axiom: the gap
from the weak clause to `¬ IsPeriodic ϑ` (`ξ' := ϑ`, see `ColleRegion.lean`) is a separate
open item.  Do not record `colle_region` as dischargeable until the substitution check above
is green.

## Closed 2026-09-17 — `ChainGeom.lean`

The conclusion is now `ColleReg.region_not_periodic_of_geom` applied to the bundle that
`exists_chainData` hands over.  No new hypothesis was invented: the geometry it needs
(`rec_p`, `dot_nJ_p`, `bottom`, and the `ℓ_J`-edge description of `S_φ`) are fields of
`ChainDataGeom`, i.e. obligations of the *constructor*, which is where Collé §3 discharges
them.  The orbit direction is `cg.vJ = v_{ℓ'} = v_{ℓ_J}`, not `vl = v_{ℓ_ι}`; see
`blueprint/NOTE.md`, entry "Claim 3.7 的轨道方向 — 2026-09-17".  `colle_region` binds the
direction existentially, so its statement is unchanged.

Measured closure: `[propext, Classical.choice, Quot.sound]`. -/
theorem region_not_periodic (cg : ChainDataGeom ξ xper vl p S gen) {K ε : ℕ}
    (hξ : IsMinimalCounterexample ξ)
    (hc_env : cg.toChainData.Env = Nivat.LE2.EnvOf (S : Set (ℤ × ℤ)))
    (hgen : Nivat.Colle.GeneratesAt ξ S gen)
    (hSgen : Nivat.Colle.IsGeneratingSet ξ S)
    (hvl_ne : vl ≠ 0) (hp_ne : p ≠ 0) (hp_per : p ∈ Per xper) (hdet_vl : det p vl = 0)
    (hxper_mem : xper ∈ orbitClosure ξ)
    (hϑ_mem : ϑ ∈ orbitClosure ξ)
    (hagree : ∀ z ∈ ⋃ i, cg.toChainData.Ahat i, ϑ z = T ((K : ℤ) • vl) xper z)
    (hϑ_periodic : PeriodicOnWith ϑ (⋃ i, cg.toChainData.Ahat i) p)
    (hshell : ∀ z ∈ cg.toChainData.shellInf ε, ϑ z = T ((K : ℤ) • vl) xper z)
    (hshell_not :
      ¬ (∀ z ∈ cg.toChainData.shellInf (ε + 1), ϑ z = T ((K : ℤ) • vl) xper z)) :
    ¬ ∃ y : Config ℤ, Colle45.IsFullyPeriodic y ∧
      ∀ (W : Finset (ℤ × ℤ)) (M : ℕ), ∃ t : ℕ, M ≤ t ∧
        ∀ z ∈ W, y z = T ((t : ℤ) • cg.vJ) ϑ z :=
  region_not_periodic_of_geom cg hp_ne hp_per hxper_mem hϑ_mem hshell hshell_not hSgen

end Nivat.ColleReg

section Receipts
/-! 接链收据（可整块删除）。 -/

#print axioms Nivat.ColleReg.wedgeResidualR_of_cone_hmono_at_shear
#print axioms Nivat.ColleReg.claim46_periodOn_coneRegion
#print axioms Nivat.ColleReg.claim46_of_case1
#print axioms Nivat.ColleReg.stage2_frame_of_shear_corner
#print axioms Nivat.ColleReg.exists_hbase_of_cone_hmono_at_shear_of_argmax
#print axioms Nivat.ColleReg.wedgeResidualR_of_stage2_frame
#print axioms Nivat.ColleReg.wedgeResidualR_of_cone_hmono_at_shear_of_argmax
#print axioms Nivat.ColleReg.hmono_shift
#print axioms Nivat.ColleReg.wedgeResidualR_of_cone_of_enveloped
#print axioms Nivat.ColleReg.wedgeResidualR_of_case1_of_cone
#print axioms Nivat.ColleReg.wedgeResidualR_of_case1_of_cone_at_base
#print axioms Nivat.ColleReg.wedgeResidualR_of_case1_of_cone_at_base_of_agree
#print axioms Nivat.ColleReg.exists_zsmul_vl_mem_Per_eta
#print axioms Nivat.ColleReg.no_edge_parallel_vl_of_erase
#print axioms Nivat.ColleReg.exists_cutLevel
#print axioms Nivat.ColleReg.halfStrip_shift
#print axioms Nivat.ColleReg.coneRegion_shift

end Receipts

