/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ShellSubStrip
import Nivat.External.Colle.ItemIIRec

/-!
# `shellSubStrip` 的 §6 归约是死路：`hcheck` 不可能只从 item (ii) 的数据证出来

集成者，2026-09-23（第 144 轮）。本文件是**内核收据**，不产生新的正面结论，
作用是关掉一条已经吃掉两条 lane 的路线，并指明漏在哪里。

## 背景

Collé 在 `scratch/b3_colle2.txt:520` 断言

> Furthermore, one has `B_i - k_i v⃗_ℓ ⊂ Â_i^{(ε)} ⊂ H_{B_i}(ℓ) - k_i v⃗_ℓ`

右半就是 `ChainDataGeom.ofPartsExhaustsInter` 的 `shellSubStrip` binder
（`ChainExhaustInter.lean`）。`w_eq_vl_or_dot_nl_w_neg`（`ShellSubStrip.lean:136`）
把它劈成两半：`w = vl` 的平行情形已由 `shellSubStrip_of_w_eq_vl`（`ShellSubStrip.lean:224`）
关掉；剩下 `dot nℓ w < 0` 的横向情形，由 `shellSubStrip_of_bounded_check`
（`ShellSubStrip.lean:312`）归约到它的 `hcheck` binder。

**本文件证明那个 `hcheck` 不可能证出来。**`shellSubStrip_of_bounded_check` 本身当然仍是
真定理（这里否掉的是它的假设，不是它的结论）；死掉的是「先归约到 `hcheck`、再用 item (ii)
补上」这条路线。

## 反例

`nℓ = (0,1)`，`cz = 0`，`vl = (1,0)`，`w = (-1,-1)`，`kk = 0`，
`A = B := Bbox`，其中 `Bbox i := ↑(AenvfixProbe.boxHP (0,1) 0 i) = [-i,i] × [0,i]`。

取这个 `B` 不是随手挑的。真实的 `B i` 是 `chB c s₀ i`（`AenvfixProbe.chB`，
`ItemIIRec.lean:187`；经 `tmp/wip/LeafAAssemble.lean:531` 接到 `ofPartsExhaustsInter` 的 `B`），
而 `stepB_spec`（`AenvfixProbe.stepB_spec`，`ItemIIRec.lean:144`）对它只给出
`↑(boxHP nℓ cz i) ⊆ stepB c s i`——一个**下界**。`Bbox` 正是这个下界取等号的情形。

喂 `i = 1`，`g = (-1,1)`，`t = 1`：前提 `1 ≤ dot (0,1) (-1,1) - 0 = 1` 成立，
结论要 `(-2,0) ∈ halfStrip (Bbox 1) (1,0)`，而 `halfStrip` 只允许 `+ℕ•(1,0)`，
第一坐标不可能降到 `-2`。

## 这个实例满足哪些前提（逐条核过，都在本文件里有 0 sorry 的引理）

* `hperp : dot nℓ vl = 0`（`ChainExhaustInter.lean`）——`hperp_inst`
* `hw : dot nℓ w < 0`（横向分支）——`hw_inst`
* `hvJ1 : 0 ≤ dot nℓ vJ1`，取 `vJ1 = (1,0)`——`hvJ1_inst`
* `hlev : ∀ z ∈ Ainf, cz ≤ dot nℓ z`，取 `Ainf = {z | 0 ≤ dot nℓ z}`——`hlev_inst`
* `hsub : ∀ i, A i ⊆ halfStrip (B i) vl`（即 `subStrip`）——`hsub_Bbox`
* `ItemII B nℓ cz`（`ItemII.lean:80`）——`itemII_Bbox`
* `Exhausts A nℓ cz`（`ItemII.lean:96`，`ofPartsExhaustsInter` 的 `hexh`）——`exhausts_Bbox`
* `subBA : ∀ i, B i ⊆ A i` / `subAB : ∀ i, A i ⊆ B (i+1)`——`subBA_Bbox` / `subAB_Bbox`

**没有**核的有两条，都不在 `shellSubStrip_of_bounded_check` 的 binder 里，但都在顶层
`ofPartsExhaustsInter` 的 binder 里：

* `envB : ∀ i, Env (B i)`，`Env = EnvOf ↑S`（`LatticeEdges.lean:2433`）。验证它要算 `E` 与
  `face` 的 `encard`，是 `LatticeEdges.lean` 量级的工作，本轮没做。
* `hhp : ∀ i, hatOf A kk vl i ⊆ halfPlaneGE nJ cJ`（`ChainExhaustInter.lean`）。这条在本实例上
  **确实为假**，而且是结构性的：`dot nJ vl < 0` 被 `lane-substrip-sign`
  （`tmp/wip/lane-substrip-sign.lean`）定死，`vl = (1,0)` 于是逼出 `nJ.1 < 0`，而
  `dot nJ` 在 `Bbox i = [-i,i] × [0,i]` 上取 `z.1 = i` 时随 `i` 趋于 `-∞`，没有固定的 `cJ` 接得住。

所以本文件**只**否掉 `shellSubStrip_of_bounded_check` 的假设，**不**接近否掉顶层 binder：
`hhp` 加上 `dot nJ vl < 0` 正是这条实例缺的东西，也正是下一步必须用上的东西。

## 与 `tmp/wip/lane-substrip-refute.lean` 的关系（这条很重要）

那份反例用 `Aex i = {|x| ≤ i², 0 ≤ y ≤ i-1}`，`x` 向宽度 `Θ(i²)`，并在自己的 scope note 里
承认：真实的 `B` 带固定窗口 `S` 的 `envB`，而 `Aex` 的宽度随 `i` 无界，不可能是任何固定窗口的
`Env`-包络，所以**那份反例没有否掉顶层 binder**，只否掉了一条 docstring 里的踏脚石。

本文件的 `Bbox i` 宽度只有 `Θ(i)`，而且它就是 `stepB_spec` 保证的那个盒子本身，
所以「宽度爆炸、不可能被包络」这条反驳对本文件不适用。这使结论从「那条踏脚石写错了」
升级为「`hcheck` 这个形状本身不对」。

（本文件**仍不**构成对顶层 `shellSubStrip` binder 的否证：`envB` 没核、`hhp` 在本实例上为假，见上。）

## 结构性原因，以及漏在哪里

`halfStrip B vl = B + ℕ•vl` 对**任何**满足 `dot n' vl ≥ 0` 的 `n'` 保持 `dot n'` 的下界
（`dot n' (b + s•vl) = dot n' b + s * dot n' vl ≥ dot n' b`）。取 `n' = (1,0)`，
`dot n' vl = 1 > 0`。于是 `B i` 上 `dot n'` 的任何极小点，在任何 `dot n' w < 0` 的 `w` 下
都会跑出半条带。这条义务只能靠「这种极小点总是太**低**、撑不起 `t ≥ 1`」活下来，
即在那里 `dot nℓ b - cz < -dot nℓ w`。盒子的左边界从底一直跑到顶
（`b = (-i,i)` 既最左又最高），所以这条退路没有。

漏在归约那一步。`hcheck` 只保留了 `sweep_param_le`（`ShellSubStrip.lean:167`）给出的标量界
`(t:ℤ) ≤ dot nℓ g - cz`，把 `shellInter` 的另一半整个丢了。真实前提是
`z = g + t•w ∈ ShellMink.shellInter (hatOf A kk vl i) (MaxEnv.shell (⋃ j, hatOf A kk vl j) vJ1 nJ cJ ε) w`，
而 `shellInter A Ainf w = reachSet A w ∩ Ainf`（`ShellMink.shellInter`，`ShellMink.lean:508`），
所以 `mem_shell`（`MaxEnv.mem_shell`，`MaximalEnveloped.lean:567`）还给出**第二个表示**

  `z = g₂ + t₂ • vJ1`，`g₂ ∈ ⋃ j, hatOf A kk vl j`，`t₂ : ℕ`，`cJ - ε ≤ dot nJ z`。

`hvJ1 : 0 ≤ dot nℓ vJ1` 正是关于这一半的符号事实，而 `hcheck` 里连 `vJ1` 都不出现。
本文件的 `z = (-2,0)` 没有被要求满足这一条——这正是它没有否掉顶层 binder 的原因，
也说明那一半就是全部剩余内容所在。

下一步必须把 §6 换成保留 `g₂ / t₂ / dot nJ` 的归约，而不是继续补 `hcheck`。
这也印证了 `AhatHeight.lean` 模块 docstring 末尾的判断（「needs `maxA`, not merely
`A i ⊆ halfStrip (B i) vl`」）：本文件的实例满足 `hsub` 而 `hcheck` 为假，正是那句话的见证。

## 一名多物（`blueprint/NOTATION.md`）

`halfStrip` 是两个同体不同名的常数：`Colle35.halfStrip`（`Lemma35.lean:404`）与
`LE2.halfStrip`（`LatticeEdges.lean:1810`）。`shellSubStrip_of_bounded_check` 用的是
`Colle35.halfStrip`，本文件一律写全名。
-/

set_option autoImplicit false

namespace Nivat.HcheckRefute

open Nivat Nivat.LE2 Nivat.Colle35

/-- 反例塔：`Bbox i = [-i,i] × [0,i]`，正是 `AenvfixProbe.boxHP (0,1) 0 i`
（`ItemIIRec.lean:89`），即 `stepB_spec`（`ItemIIRec.lean:144`）给真实 `B i` 的那个下界
取等号的情形。 -/
def Bbox (i : ℕ) : Set (ℤ × ℤ) := ↑(Nivat.AenvfixProbe.boxHP ((0 : ℤ), (1 : ℤ)) 0 i)

theorem mem_Bbox {i : ℕ} {z : ℤ × ℤ} :
    z ∈ Bbox i ↔ (-(i : ℤ) ≤ z.1 ∧ z.1 ≤ i) ∧ (-(i : ℤ) ≤ z.2 ∧ z.2 ≤ i) ∧
      (0 : ℤ) ≤ dot ((0 : ℤ), (1 : ℤ)) z := by
  simp only [Bbox]
  exact Nivat.AenvfixProbe.mem_boxHP

/-- `dot (0,1) z = z.2`，本文件反复用。 -/
theorem dot_e2 (z : ℤ × ℤ) : dot ((0 : ℤ), (1 : ℤ)) z = z.2 := by simp [dot]

/-! ### 本实例满足 `shellSubStrip_of_bounded_check` 与 `ofPartsExhaustsInter` 的哪些前提 -/

/-- `hperp`（`ChainExhaustInter.lean`）：`dot nℓ vl = 0`。 -/
theorem hperp_inst : dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) = 0 := by simp [dot]

/-- 横向分支（`w_eq_vl_or_dot_nl_w_neg`，`ShellSubStrip.lean:136`）：`dot nℓ w < 0`。 -/
theorem hw_inst : dot ((0 : ℤ), (1 : ℤ)) ((-1 : ℤ), (-1 : ℤ)) < 0 := by norm_num [dot]

/-- `hvJ1`（`shellSubStrip_of_bounded_check`）：取 `vJ1 = (1,0)`。 -/
theorem hvJ1_inst : (0 : ℤ) ≤ dot ((0 : ℤ), (1 : ℤ)) ((1 : ℤ), (0 : ℤ)) := by simp [dot]

/-- `hlev`（`shellSubStrip_of_bounded_check`）：取 `Ainf = {z | 0 ≤ dot nℓ z}`。 -/
theorem hlev_inst : ∀ z ∈ {z : ℤ × ℤ | (0 : ℤ) ≤ dot ((0 : ℤ), (1 : ℤ)) z},
    (0 : ℤ) ≤ dot ((0 : ℤ), (1 : ℤ)) z := fun _ hz => hz

/-- `hsub` / `subStrip`：`A i ⊆ halfStrip (B i) vl`，这里 `A = B` 故取 `t = 0`。 -/
theorem hsub_Bbox (i : ℕ) : Bbox i ⊆ Nivat.Colle35.halfStrip (Bbox i) ((1 : ℤ), (0 : ℤ)) :=
  fun z hz => ⟨z, hz, 0, by simp⟩

/-- `subBA`（`ChainExhaustInter.lean`）：`B i ⊆ A i`，这里 `A = B`。 -/
theorem subBA_Bbox (i : ℕ) : Bbox i ⊆ Bbox i := subset_rfl

/-- `subAB`（`ChainExhaustInter.lean`）：`A i ⊆ B (i+1)`，盒子对 `i` 单调。 -/
theorem subAB_Bbox (i : ℕ) : Bbox i ⊆ Bbox (i + 1) := by
  intro z hz
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := mem_Bbox.mp hz
  refine mem_Bbox.mpr ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, h5⟩ <;> push_cast <;> omega

/-- `ItemII B nℓ cz`（`ItemII.lean:80`）：`|z.1|, |z.2| ≤ i-1` 蕴含 `z ∈ Bbox i`。 -/
theorem itemII_Bbox : Nivat.Colle35.ItemII Bbox ((0 : ℤ), (1 : ℤ)) 0 := by
  intro i z h1 h2 hz
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  obtain ⟨h2a, h2b⟩ := abs_le.mp h2
  exact mem_Bbox.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, hz⟩

/-- `Exhausts A nℓ cz`（`ItemII.lean:96`，即 `ofPartsExhaustsInter` 的 `hexh`）：
`⋃ i, Bbox i = {z | 0 ≤ z.2}`。见证指标取 `i := |z.1| + z.2`。 -/
theorem exhausts_Bbox : Nivat.Colle35.Exhausts Bbox ((0 : ℤ), (1 : ℤ)) 0 := by
  unfold Nivat.Colle35.Exhausts
  ext z
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi⟩
    exact (mem_Bbox.mp hi).2.2
  · intro hz
    rw [dot_e2] at hz
    -- `omega` 原生认识 `Int.natAbs` / `Int.toNat`；这里刻意不用 `push_cast`，
    -- 因为它会把 `(z.1.natAbs : ℤ)` 改写成 `|z.1|`，反而把 `omega` 挡在外面。
    have hcast : ((z.1.natAbs + z.2.toNat : ℕ) : ℤ)
        = (z.1.natAbs : ℤ) + (z.2.toNat : ℤ) := Nat.cast_add _ _
    refine ⟨z.1.natAbs + z.2.toNat,
      mem_Bbox.mpr ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, by rw [dot_e2]; exact hz⟩⟩ <;>
      rw [hcast] <;> omega

/-! ### 反例本体 -/

/-- `kk = 0` 时 `hatOf` 是恒等：`hatOf Bbox 0 vl i = Bbox i`。 -/
theorem hatOf_zero (i : ℕ) :
    Nivat.Colle35.hatOf Bbox (fun _ => 0) ((1 : ℤ), (0 : ℤ)) i = Bbox i := by
  ext z
  simp [Nivat.Colle35.hatOf]

theorem g_mem : ((-1 : ℤ), (1 : ℤ)) ∈
    Nivat.Colle35.hatOf Bbox (fun _ => 0) ((1 : ℤ), (0 : ℤ)) 1 := by
  rw [hatOf_zero]
  exact mem_Bbox.mpr ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, by norm_num [dot]⟩

/-- `(-2,0) ∉ halfStrip (Bbox 1) (1,0)`：`+ℕ•(1,0)` 只让第一坐标变大，而 `Bbox 1` 的
第一坐标 `≥ -1`。 -/
theorem not_mem : ((-2 : ℤ), (0 : ℤ)) ∉
    Nivat.Colle35.halfStrip (Bbox 1) ((1 : ℤ), (0 : ℤ)) := by
  rintro ⟨b, hb, s, heq⟩
  obtain ⟨⟨hb1, -⟩, -, -⟩ := mem_Bbox.mp hb
  have hfst := congrArg Prod.fst heq
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, mul_one] at hfst
  have hs0 : (0 : ℤ) ≤ (s : ℤ) := Int.natCast_nonneg _
  norm_num at hb1
  omega

/-- **`hcheck` 为假的内核见证。**假设部分是 `shellSubStrip_of_bounded_check`
（`ShellSubStrip.lean:312`）的 `hcheck` binder 在
`A = B := Bbox`，`kk := 0`，`nℓ := (0,1)`，`cz := 0`，`vl := (1,0)`，`w := (-1,-1)`
上的逐字实例化；喂 `i = 1`，`g = (-1,1)`，`t = 1` 得到 `False`。

同一实例上 `hlev` / `hvJ1` / `hw` / `hsub` / `ItemII` / `Exhausts` / `subBA` / `subAB`
全部成立（本文件上方各引理），所以 `hcheck` 不可能从这些数据推出来。
没核的前提是 `envB`、以及顶层才有的 `hhp`（后者在本实例上为假；见模块 docstring）。 -/
theorem hcheck_false
    (hcheck : ∀ i : ℕ, ∀ g ∈ Nivat.Colle35.hatOf Bbox (fun _ => 0) ((1 : ℤ), (0 : ℤ)) i,
      ∀ t : ℕ, 1 ≤ t →
      (t : ℤ) ≤ dot ((0 : ℤ), (1 : ℤ)) g - 0 →
      g + (t : ℤ) • ((((-1 : ℤ), (-1 : ℤ))) : ℤ × ℤ) + ((0 : ℕ) : ℤ) • ((1 : ℤ), (0 : ℤ)) ∈
        Nivat.Colle35.halfStrip (Bbox i) ((1 : ℤ), (0 : ℤ))) : False := by
  have h := hcheck 1 ((-1 : ℤ), (1 : ℤ)) g_mem 1 (le_refl 1) (by norm_num [dot])
  have heq : ((-1 : ℤ), (1 : ℤ)) + ((1 : ℕ) : ℤ) • ((((-1 : ℤ), (-1 : ℤ))) : ℤ × ℤ)
      + ((0 : ℕ) : ℤ) • (((1 : ℤ), (0 : ℤ)) : ℤ × ℤ) = ((-2 : ℤ), (0 : ℤ)) := by
    ext <;> simp
  rw [heq] at h
  exact not_mem h

/-- 同一反例对只在 `B i` 上取值的那个版本（把 `hcheck` 用 `hperp` + `subStrip` 折到
`b ∈ B i` 上、并把标量界收紧成 `t * (-dot nℓ w) ≤ dot nℓ b - cz` 后得到的形状）。
收紧后的前提更强，所以这条比 `hcheck_false` 更强。 -/
theorem hbase_false
    (hbase : ∀ i : ℕ, ∀ b ∈ Bbox i, ∀ t : ℕ, 1 ≤ t →
      (t : ℤ) * (- dot ((0 : ℤ), (1 : ℤ)) ((-1 : ℤ), (-1 : ℤ))) ≤
        dot ((0 : ℤ), (1 : ℤ)) b - 0 →
      b + (t : ℤ) • ((((-1 : ℤ), (-1 : ℤ))) : ℤ × ℤ) ∈
        Nivat.Colle35.halfStrip (Bbox i) ((1 : ℤ), (0 : ℤ))) : False := by
  have hb : ((-1 : ℤ), (1 : ℤ)) ∈ Bbox 1 := by rw [← hatOf_zero 1]; exact g_mem
  have h := hbase 1 ((-1 : ℤ), (1 : ℤ)) hb 1 (le_refl 1) (by norm_num [dot])
  have heq : ((-1 : ℤ), (1 : ℤ)) + ((1 : ℕ) : ℤ) • ((((-1 : ℤ), (-1 : ℤ))) : ℤ × ℤ)
      = ((-2 : ℤ), (0 : ℤ)) := by ext <;> simp
  rw [heq] at h
  exact not_mem h

end Nivat.HcheckRefute

#print axioms Nivat.HcheckRefute.itemII_Bbox
#print axioms Nivat.HcheckRefute.exhausts_Bbox
#print axioms Nivat.HcheckRefute.hcheck_false
#print axioms Nivat.HcheckRefute.hbase_false
