/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: lane-tower-hlev
-/
import Nivat.External.Colle.EscapeW
import Nivat.External.Colle.ItemIIChain

/-!
# `escapeW` 接线：把 `ChainDataGeomParts.escapeW` 从 binder 表里删掉

Lane `lane-tower-hlev`，第 227 轮（2026-09-25）。0 `sorry`。
本文件 `import` 两条（与 `grep -n "^import"` 逐字一致，`PROTOCOL §57`）：
`EscapeW` / `ItemIIChain`。**不** `import`
`RegionSteps` / `ColleRegion` / `Case2WindowProbe` / `NfpLPreamble`。

## 本文件交什么

第 226 轮的前提表结论是：**`escapeW` 相对于 `ChainDataGeomParts` 的 binder 表，剩余欠账是
空集**；唯一的真残差是 `I₀` 的量词位置——生产者
`Nivat.LaneTowerHlevEscPos.exists_I₀_escapeW`（`EscapeW.lean`）交的是 `∃ I₀`，
而消费者当时收的是一条**输入** binder。

2026-09-25 集成者把 `I₀` 改成 `ChainDataGeomParts` 的**字段**
（`ChainPartsFeed.lean`，字段名 `I₀`），字段即「生产者自己选」，那条残差因此关闭。
本文件把关闭这件事做成内核见证，共三步：

* §2 `escapeW_of_parts_binders`：前提**逐条**是 `ChainDataGeomParts` 的同名字段
  （`Env` 已钉成 `EnvOf ↑S`，与字段一致），结论是 `∃ I₀, <escapeW 字段的形状>`。
* §3 `exists_common_I₀`：`escapeW` / `shellSubStrip` / `fillCover` 三条字段的尾部
  对 `I₀` 反单调（`EscapeW` 的 `tail_mono_I₀`），各给一个阈值取 `max` 即得公共 `I₀`。
* §4 `chainDataGeomParts_of_chain_escapeW_free`：`ItemIIChain.chainDataGeomParts_of_chain`
  的**去 `escapeW` 形**——binder 表里不再有 `I₀`，也不再有 `escapeW`，
  `shellSubStrip` / `fillCover` 改收 `∃ I₀` 形。这一条是真正的接线：
  它的类型由内核对着 `ChainDataGeomParts` 的字段类型查，逐字符对不上就编不过。

## 原文对应

`b3_colle2.txt:530`（逃出点落在 `shellInf ε` 内）＋ `:492`（sweep 方向的符号）；
守卫与 `I₀` 的出处是 `:520`（「for an appropriate `ε ∈ ℕ` fixed and all `i` sufficiently
large」／「consider a constant `I₀ ∈ ℕ`」）与 `:524`（逐字「if we consider
`i ≥ max{i₀, I₀}`」）。`w` 是 `:518` 的 `−v⃗_{ℓ_{J+1}}`。

⚠ 一名多物（`NOTATION.md` 的 `vJ1` / `nJ` / `nprevJ` 那节）：`vJ1 := v⃗_{ℓ_{J−1}}`，
而 `w := −v⃗_{ℓ_{J+1}}`，**下标差 2，名字暗示下一步而物是上一步**。本文件所有
`w` 都是后者，所有 `vJ1` 都是前者。

## 辖域（`PROTOCOL §40`，必须分开讲）

1. `EscapeW.lean` 抬头那句「没用到格凸性」，辖域是 **`exists_I₀_escapeW` 本身**
   （它把 `rec_vJ` 当前提收）。§2 把 `rec_vJ` 也展开成字段之后，格凸性经
   `latticeConvex_iUnion_hatOf`（`ChainAssemble.lean`）进来，吃掉 `maxA` / `hfin` /
   `AhatMono` 三条。两句话不矛盾。
2. 「`escapeW` 不需要守卫」≠「守卫惰性」。后者是**假的**
   （`envOf_guard_false_on_box`，第 163 轮）。本文件只主张前者：守卫原样收下、原样不用。
3. §2 用**不到**的字段：`envShift` / `envB` / `subBA` / `subAB` / `nJ_prim` /
   `gen_eq` / `shellEnv` / `shellSubStrip` / `fillCover` / `cL` 那三条。
   ⟹ `escapeW` **不堵在 `shellEnv` 上**（与 `PROTOCOL §78` 同向）。
4. `EscapeWReduce` / `EscapeWSubset` 打的是**旧**签名（`∀ i ε, 0 < ε → …`，无 `I₀`、
   无守卫），**不是**现行字段的产者；本文件不经它们。
-/

set_option autoImplicit false

namespace Nivat.LaneTowerHlevEscWire

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.Colle35 Nivat.ChainAsm

/-! ## §1  记号

下面统一写 `Ah i := hatOf A kk vl i`（`ChainDataGeomParts` 的字段里也是这个形）。
`Ainf := ⋃ i, Ah i`。 -/

/-! ## §2  `escapeW` 的产者，前提逐条是 `ChainDataGeomParts` 的字段

`Env` 在 `ChainDataGeomParts` 里被钉成 `EnvOf (↑S : Set (ℤ × ℤ))`
（`ChainPartsFeed.lean` 的 `maxA` / `envB` 两条字段），所以这里直接写死，
不再留 `hEnv` 形参——留着反而会让「本条能否喂给字段」多一步人工核对。 -/

/-- ⭐ **`escapeW` 不是独立义务。**前提逐条是 `ChainDataGeomParts`
（`ChainPartsFeed.lean`）的同名字段：`maxA` / `AhatMono` / `hsweep` / `hfin` / `hhp` /
`hswept` / `ahat_nonempty` / `hsweepW` / `F`（给 `dot_nJ_vJ`）/ `vJ_prim` / `bottom` /
`rec_p` / `dot_nJ_p`；结论是 `∃ I₀, <escapeW 字段的形状>`，而 `I₀` 自 2026-09-25 起
就是该结构的字段，故 `∃` 正是字段该收的形。

原文：`b3_colle2.txt:530`（结论）＋ `:520`／`:524`（`I₀` 与守卫）＋ `:492`（符号）。

⚠ `bottom` 只有**前两个合取**被用到（经 `rec_vJ_of_bottom`，`ItemII.lean`，其体内
`obtain ⟨z₀, L, hz₀, hline, -, -⟩ := bottom 0`），以及第一个合取在一般 `ε` 上的那份。
第 3、4 两个合取本条**不碰**——它们的消费者在别处。 -/
theorem escapeW_of_parts_binders {α : Type*}
    (η xper : Config α) (vl p : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ)
    (maxA : ∀ i, IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ))) (canonA η xper vl B u i) (A i))
    (AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j)
    (vJ1 nJ : ℤ × ℤ) (cJ : ℤ)
    (hsweep : dot nJ vJ1 < 0)
    (hfin : ∀ i, (hatOf A kk vl i).Finite)
    (hhp : ∀ i, hatOf A kk vl i ⊆ halfPlaneGE nJ cJ)
    (hswept : SweptClosed (⋃ i, hatOf A kk vl i) vJ1 nJ cJ)
    (ahat_nonempty : (⋃ i, hatOf A kk vl i).Nonempty)
    (w : ℤ × ℤ) (hsweepW : dot nJ w < 0)
    (vJ : ℤ × ℤ) (F : FaceBlock S nJ vJ) (vJ_prim : Primitive vJ)
    (bottom : ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ reachSet (⋃ i, hatOf A kk vl i) vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k →
        z₀ + k • vJ + (b - F.a) ∈ reachSet (⋃ i, hatOf A kk vl i) vJ1) ∧
      (∀ z ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ (ε + 1),
        z ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε ∨
          ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ))
    (rec_p : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + p ∈ ⋃ i, hatOf A kk vl i)
    (dot_nJ_p : dot nJ p ≠ 0) :
    ∃ I₀ : ℕ, ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ)) (ShellMink.shellInter (hatOf A kk vl i)
        (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w)) →
      ∀ i, max i₀ I₀ ≤ i → ∃ g ∈ hatOf A kk vl i, ∃ t : ℕ,
        g + (t : ℤ) • w ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε ∧
        g + (t : ℤ) • w ∉ hatOf A kk vl i := by
  refine Nivat.LaneTowerHlevEscPos.exists_I₀_escapeW
    (Env := EnvOf (↑S : Set (ℤ × ℤ))) AhatMono hhp hswept
    ahat_nonempty hsweep hsweepW F.dot_nJ_vJ vJ_prim.ne_zero ?_ rec_p dot_nJ_p ?_
  · exact rec_vJ_of_bottom
      (latticeConvex_iUnion_hatOf η xper vl S (EnvOf (↑S : Set (ℤ × ℤ))) B A u kk rfl
        maxA hfin AhatMono)
      hsweep (fun _ hg => Set.iUnion_subset hhp hg) hswept F.dot_nJ_vJ bottom
  · intro ε
    obtain ⟨z₀, L, h1, h2, -, -⟩ := bottom ε
    exact ⟨z₀, L, h1, h2⟩

/-! ## §3  `I₀` 合流

`escapeW` / `shellSubStrip` / `fillCover` 三条字段的外壳同形
（`∀ ε i₀, 0 < ε → 守卫 → ∀ i, max i₀ I₀ ≤ i → …`），`I₀` 只出现在前件、且是 `max`
的一支 ⟹ 三条尾部对 `I₀` 都**反单调**（`EscapeW` 的 `tail_mono_I₀`）。
三条守卫写成三个不同的 `G`：逐字对齐时它们确实是同一条，但本引理不需要它们相同，
**不假设相同是为了不比原文强**（硬规矩 5）。 -/

/-- **三条尾部合流到一个 `I₀`。**各自阈值取 `max`。 -/
theorem exists_common_I₀ {Pe Ps Pf : ℕ → ℕ → ℕ → Prop} {Ge Gs Gf : ℕ → ℕ → Prop}
    (he : ∃ I₀ : ℕ, ∀ ε i₀ : ℕ, 0 < ε → Ge ε i₀ → ∀ i, max i₀ I₀ ≤ i → Pe ε i₀ i)
    (hs : ∃ I₀ : ℕ, ∀ ε i₀ : ℕ, 0 < ε → Gs ε i₀ → ∀ i, max i₀ I₀ ≤ i → Ps ε i₀ i)
    (hf : ∃ I₀ : ℕ, ∀ ε i₀ : ℕ, 0 < ε → Gf ε i₀ → ∀ i, max i₀ I₀ ≤ i → Pf ε i₀ i) :
    ∃ I₀ : ℕ,
      (∀ ε i₀ : ℕ, 0 < ε → Ge ε i₀ → ∀ i, max i₀ I₀ ≤ i → Pe ε i₀ i) ∧
      (∀ ε i₀ : ℕ, 0 < ε → Gs ε i₀ → ∀ i, max i₀ I₀ ≤ i → Ps ε i₀ i) ∧
      (∀ ε i₀ : ℕ, 0 < ε → Gf ε i₀ → ∀ i, max i₀ I₀ ≤ i → Pf ε i₀ i) := by
  obtain ⟨Ie, hIe⟩ := he
  obtain ⟨Is, hIs⟩ := hs
  obtain ⟨If, hIf⟩ := hf
  refine ⟨max Ie (max Is If), ?_, ?_, ?_⟩
  · exact fun ε i₀ hε hG =>
      Nivat.LaneTowerHlevEscPos.tail_mono_I₀ (le_max_left Ie (max Is If)) (hIe ε i₀ hε hG)
  · exact fun ε i₀ hε hG =>
      Nivat.LaneTowerHlevEscPos.tail_mono_I₀
        (le_trans (le_max_left Is If) (le_max_right Ie (max Is If))) (hIs ε i₀ hε hG)
  · exact fun ε i₀ hε hG =>
      Nivat.LaneTowerHlevEscPos.tail_mono_I₀
        (le_trans (le_max_right Is If) (le_max_right Ie (max Is If))) (hIf ε i₀ hε hG)

/-! ## §4  接线：`chainDataGeomParts_of_chain` 的去 `escapeW` 形

下面这条与 `ItemIIChain.chainDataGeomParts_of_chain` 的 binder 表**只差三处**：
删掉 `I₀`、删掉 `escapeW`，并把 `shellSubStrip` / `fillCover` 改收 `∃ I₀` 形
（`shellEnv` 里没有 `I₀`，不动）。其余 binder 逐字照抄。

⚠ `ChainDataGeomParts` 是 `Type`，不是 `Prop`，所以三条 `∃ I₀` 必须用
`.choose` / `.choose_spec` 拆，**不能 `obtain`**（`PROTOCOL §88`）。 -/

/-- ⭐ **接线形**：`escapeW` 与 `I₀` 都不再是 binder。

`escapeW` 由 §2 从别的字段自动补上；`I₀` 取 §2 / `shellSubStrip` / `fillCover`
三个阈值的 `max`，三条同时在它上面成立（§3）。

与 `ItemIIChain.chainDataGeomParts_of_chain` 的差：删 `I₀`、删 `escapeW`，
`shellSubStrip` / `fillCover` 收 `∃ I₀` 形。这条 `def` 编得过本身就是
「`escapeW` 的形状与字段逐字符一致」的内核见证。 -/
noncomputable def chainDataGeomParts_of_chain_escapeW_free
    (ξ xper : Config ℤ) (vl p : ℤ × ℤ) (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ)
    (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ)
    (envB : ∀ i, EnvOf (↑S : Set (ℤ × ℤ)) (B i))
    (finB : ∀ i, (B i).Finite)
    (maxA : ∀ i, IsMaxEnvIn (EnvOf (↑S : Set (ℤ × ℤ))) (canonA ξ xper vl B u i) (A i))
    (subBA : ∀ i, B i ⊆ A i) (subAB : ∀ i, A i ⊆ B (i + 1))
    (kk : ℕ → ℕ)
    (AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j)
    (vJ1 nJ : ℤ × ℤ) (cJ : ℤ)
    (hsweep : dot nJ vJ1 < 0)
    (hhp : ∀ i, hatOf A kk vl i ⊆ halfPlaneGE nJ cJ)
    (hswept : MaxEnv.SweptClosed (⋃ i, hatOf A kk vl i) vJ1 nJ cJ)
    (ahat_nonempty : (⋃ i, hatOf A kk vl i).Nonempty)
    (w : ℤ × ℤ) (hsweepW : dot nJ w < 0)
    (hshellSubStrip : ∃ I₀ : ℕ, ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ)) (ShellMink.shellInter (hatOf A kk vl i)
        (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w)) →
      ∀ i, max i₀ I₀ ≤ i →
      ShellMink.shellInter (hatOf A kk vl i)
          (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w ⊆
        {z | z + (kk i : ℤ) • vl ∈ Colle35.halfStrip (B i) vl})
    (shellEnv : ∃ ε i₀, 0 < ε ∧
      ∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ)) (ShellMink.shellInter (hatOf A kk vl i)
        (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w))
    (hfillCover : ∃ I₀ : ℕ, ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → EnvOf (↑S : Set (ℤ × ℤ)) (ShellMink.shellInter (hatOf A kk vl i)
        (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w)) →
      ∀ i, max i₀ I₀ ≤ i →
      ShellMink.shellInter (hatOf A kk vl i)
          (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w ⊆
        {z | Colle37.GenClosure S (hatOf A kk vl i ∪
          ShellMink.shellInter (hatOf A kk vl i₀)
            (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w) z})
    (vJ : ℤ × ℤ) (F : Colle35.FaceBlock S nJ vJ)
    (gen_eq : gen = F.a') (vJ_prim : Primitive vJ) (nJ_prim : Primitive nJ)
    (bottom : ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ MaxEnv.reachSet (⋃ i, hatOf A kk vl i) vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k →
        z₀ + k • vJ + (b - F.a) ∈ MaxEnv.reachSet (⋃ i, hatOf A kk vl i) vJ1) ∧
      (∀ z ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ (ε + 1),
        z ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε ∨
          ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ))
    (rec_p : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + p ∈ ⋃ i, hatOf A kk vl i)
    (dot_nJ_p : dot nJ p ≠ 0)
    (cL : ℤ)
    (ahat_halfPlane_L : ∀ g ∈ ⋃ i, hatOf A kk vl i, cL ≤ dot (det p vJ • (-p.2, p.1)) g)
    (ahat_attained_L : ∃ g ∈ ⋃ i, hatOf A kk vl i, dot (det p vJ • (-p.2, p.1)) g = cL)
    (nfp_L : ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
      PeriodicOnWith xper {z | cL ≤ dot (det p vJ • (-p.2, p.1)) z} h ∧
      PeriodicOnWith xper {z | cL ≤ dot (det p vJ • (-p.2, p.1)) z} h') :
    Nivat.ChainAsm.Aparts.ChainDataGeomParts ξ xper vl p S gen :=
  let hfin : ∀ i, (hatOf A kk vl i).Finite :=
    hatOf_finite kk vl (fun i => (finB (i + 1)).subset (subAB i))
  let he := escapeW_of_parts_binders ξ xper vl p S B A u kk maxA AhatMono vJ1 nJ cJ
    hsweep hfin hhp hswept ahat_nonempty w hsweepW vJ F vJ_prim bottom rec_p dot_nJ_p
  let Ie := he.choose
  let Is := hshellSubStrip.choose
  let If := hfillCover.choose
  Nivat.ItemIIChain.chainDataGeomParts_of_chain ξ xper vl p S gen B A u envB finB maxA
    subBA subAB kk AhatMono vJ1 nJ cJ hsweep hhp hswept ahat_nonempty w hsweepW
    (max Ie (max Is If))
    (fun ε i₀ hε hG =>
      Nivat.LaneTowerHlevEscPos.tail_mono_I₀ (le_max_left Ie (max Is If))
        (he.choose_spec ε i₀ hε hG))
    (fun ε i₀ hε hG =>
      Nivat.LaneTowerHlevEscPos.tail_mono_I₀
        (le_trans (le_max_left Is If) (le_max_right Ie (max Is If)))
        (hshellSubStrip.choose_spec ε i₀ hε hG))
    shellEnv
    (fun ε i₀ hε hG =>
      Nivat.LaneTowerHlevEscPos.tail_mono_I₀
        (le_trans (le_max_right Is If) (le_max_right Ie (max Is If)))
        (hfillCover.choose_spec ε i₀ hε hG))
    vJ F gen_eq vJ_prim nJ_prim bottom rec_p dot_nJ_p cL ahat_halfPlane_L ahat_attained_L nfp_L

/-! ## §5  `w` 的共线情形：binder 表自己排掉了另一半

2026-09-25 裁决是 `w := −v⃗_{ℓ_{J+1}}`（横截）：`w := vJ1` 会把交集对象塌成单次 sweep
（`ShellMink.lean` 的 `shellInter_vJ1_eq`），而那一侧被 `FillCoverWitness` §1 的内核反例否掉。
⟹ 共线的两个符号里，`+vJ1` 已被反例否掉。

下面这条补另一半：`w := -vJ1` **根本不满足 binder 表**。`hsweep : dot nJ vJ1 < 0` 与
`hsweepW : dot nJ w < 0` 是两条独立字段，取 `w = -vJ1` 时后者要求 `0 < dot nJ vJ1`，
与前者直接撞。⟹ **共线情形整个关闭**，不留第三种共线取法。

⚠ 本条否掉的是 Lean 侧那个共线取法，**不是**裁决：`w := −v⃗_{ℓ_{J+1}}` 与
`-vJ1 = -v⃗_{ℓ_{J−1}}` 下标差 2，是不同向量。 -/

/-- **`w = -vJ1` 与 binder 表不相容。**只用 `hsweep` 与 `hsweepW` 两条字段。 -/
theorem not_w_eq_neg_vJ1 {vJ1 nJ w : ℤ × ℤ}
    (hsweep : dot nJ vJ1 < 0) (hsweepW : dot nJ w < 0) : w ≠ -vJ1 := by
  intro h
  have hneg : dot nJ (-vJ1) = - dot nJ vJ1 := by
    simp only [dot, Prod.fst_neg, Prod.snd_neg]; ring
  rw [h, hneg] at hsweepW
  linarith

end Nivat.LaneTowerHlevEscWire

#print axioms Nivat.LaneTowerHlevEscWire.escapeW_of_parts_binders
#print axioms Nivat.LaneTowerHlevEscWire.exists_common_I₀
#print axioms Nivat.LaneTowerHlevEscWire.chainDataGeomParts_of_chain_escapeW_free
#print axioms Nivat.LaneTowerHlevEscWire.not_w_eq_neg_vJ1
