/-
# `chainFull` 在 `k` 上单调递增 —— 洞 2 的破口 (A) 由此定向

**为什么有这个文件。** 洞 2（`RegionSteps.exists_cutResidualR_of_claim46` 里的 `hstrict`，
`RegionSteps.lean:2527`）当前的状态是一条**正面矛盾**：(c) 段给出 `hstrict ⟺ I_paper = ι−m+1`
＝ `b3_colle2.txt:814` 区间的**下端**，而 Claim 4.10 给**上端** `ι−1`。破口只有四个 (A)–(D)，
其中承重的是

> (A) 字典方向 `I_paper = ι−1−I_lean` 反了（承重的是 lane-towerpkg 报的未验建模选择 (u3)：
>     `coneRegion B vl u' = 𝓡_{ι−1}`）。

本文件把 (A) 所依赖的**链侧**算术钉成内核事实。

## 链侧事实（本文件所证）

`chainFull B vl u' b₀ = L1Region.cut (wedgeFull B vl u') (expNormal u' vl) (expLevel u' vl b₀)`
（`L1RegionBuild.lean:305`），而
`cut Rinf m lev n = Rinf ∩ halfPlaneGE m (lev n)`（`L1Region.lean:197`）、
`halfPlaneGE n c = {z | c ≤ dot n z}`（`LatticeEdges.lean:1836`）、
`expLevel u' vl b₀ n = dot (expNormal u' vl) b₀ - (n : ℤ)` 是 **`Antitone`**
（`expLevel_antitone`，`L1RegionBuild.lean`）。

⟹ `n` 增大 ⟹ 截断电平**下降** ⟹ 约束 `lev n ≤ dot m z` **变弱** ⟹ 集合**变大**：

    cut_mono        : Antitone lev → Monotone (L1Region.cut Rinf m lev)
    chainFull_mono  : Monotone (ColleReg.chainFull B vl u' b₀)
    chainFull_zero_subset : chainFull B vl u' b₀ 0 ⊆ chainFull B vl u' b₀ k

⭐ 树里**原先没有**这条单调性（`chainFull` 的所有既有引理都只谈单个 `k` 或 `k = 0`）。

## ⟹ 对破口 (A) 的意思：⛔ **本文件初稿在这里写错了，已自撤**

初稿曾论证：`coneRegion` 不带下标（`ConeRegion.lean:138`，它只吃 `B`/`vl`/`u'`），而链侧有
`chainFull … 0 ⊆ coneRegion`（`ChainConeFit.lean:52`）与
`ConeHbase.not_chainFull_subset_coneRegion`（`ConeHbase.lean:208`）一夹，配本文件的单调性
⟹ `coneRegion` 只能对应这族的**最小**成员 ⟹ 配原文 `:806` 的递降 `R_{ι−1} ⊂ ⋯ ⊂ R_{ι−m+1}`
⟹ 字典必须保序反转 ⟹ 破口 (A)（「方向反了」）没有立足点。

🔴 **这条推理作废。** 我按自己写下的射程自限去核了那个反例的机制（`ConeHbase.lean:198-203`
的 docstring ＋ 证明体，亲读），结论与初稿相反：**不含的原因不是「层级不够」，是「单边 vs 双边」**。

> 见证 `B = {(0,0)}`、`vl = (1,0)`、`u' = (0,-1)`、`b₀ = (0,0)`、`k = 1`。点 `(-1,0)` 活过了
> `expNormal` 截断，而 `coneRegion B vl u'` **只朝 `+vl` 扫**，故其每点第一坐标 `≥ 0`。
> 原文侧：`b3_colle2.txt:414`、`:784` —— `H_B(ℓ)` 与 `𝓡_{ι−1}` **都是 `ℤ₊`-扫**；
> 而 `chainFull` 是 `wedgeFull` 的截断，`wedgeFull` 扫 **`±vl`**（`L1RegionBuild.lean:230`），
> 截断只把 `vl`-坐标从下方界住，**并不界在 `0`**。

⟹ 这是**定性**失配，不是层级失配。夹逼给不出「`coneRegion` ＝ 最小成员」，
因此**推不出**字典的定向，**(A) 没有被否掉**。四个破口 (A)–(D) 全部照旧。

## ⭐ 但单调性在这里换来一条更强的否定结论（本文件所证）

既然障碍是单边性而非层级，那么「把 `k` 调大调小」这条逃生口应当整条关闭。单调性正好给出这一步：

    not_chainFull_subset_coneRegion_all :
      ∃ B vl u' b₀ k₀, det u' vl = 1 ∧ b₀ ∈ B ∧ B.Finite ∧
        ∀ k, k₀ ≤ k → ¬ (chainFull B vl u' b₀ k ⊆ coneRegion B vl u')

证法一行：`chainFull … k₀ ⊆ chainFull … k`（`chainFull_mono`），故 `k` 档若含于 `coneRegion`
则 `k₀` 档亦含，与既有反例冲突。⟹ 把 `ConeHbase.not_chainFull_subset_coneRegion` 的
「某个 `k`」升成「`k₀` 以上全部 `k`」。⚠ 口径：`ConeHbase` 那条的 `k` 在存在量词下，所以这里
只能把 `k₀` 一并存在化；该文件 `:198` 的 docstring 自述见证取 `k = 1`，**若**如此则实际射程
是 `∀ k ≥ 1`，但那是 docstring 不是内核内容，故签名不写 `1`。
⛔ 低档**不**在结论里，且不该在——`ChainConeFit.lean:52` 在额外前提（`of_argmax`）下证的正是
`chainFull … 0 ⊆ coneRegion`。⟹ **`hchain` 那条 binder 只在低档有希望，高档整段是死的**，
这是本文件对洞 2 的实际贡献。

⛔ **射程自限（PROTOCOL §15 / §51）**：本文件证的是上面四条链侧命题。关于原文 `:414` / `:784` /
`:806` 的三处引文取自 `ConeHbase.lean` 的 docstring 与 `RegionSteps.lean:2527` 一带的批注
（前者标明是亲读），**我本轮没有重新亲读原文**；(A)–(D) 的裁决不因本文件移动。
-/
import Nivat.External.Colle.L1RegionBuild
import Nivat.External.Colle.ConeHbase

namespace Nivat.ChainFullMono

open Nivat Nivat.LE2

/-- **`cut` 对反调电平是单调的。** `cut Rinf m lev n = Rinf ∩ {z | lev n ≤ dot m z}`；
`lev` 反调 ⟹ `n` 大时门槛低 ⟹ 集合大。 -/
theorem cut_mono {Rinf : Set (ℤ × ℤ)} {m : ℤ × ℤ} {lev : ℕ → ℤ} (hlev : Antitone lev) :
    Monotone (Nivat.L1Region.cut Rinf m lev) := by
  intro a b hab z hz
  exact ⟨hz.1, le_trans (hlev hab) hz.2⟩

/-- ⭐ **`chainFull` 在截断下标上单调递增。** 树里原先没有这条。 -/
theorem chainFull_mono (B : Set (ℤ × ℤ)) (vl u' b₀ : ℤ × ℤ) :
    Monotone (Nivat.ColleReg.chainFull B vl u' b₀) :=
  cut_mono (Nivat.ColleReg.expLevel_antitone u' vl b₀)

/-- `k = 0` 那一档是整族的**最小**成员——(A) 的定向就压在这一条上。 -/
theorem chainFull_zero_subset (B : Set (ℤ × ℤ)) (vl u' b₀ : ℤ × ℤ) (k : ℕ) :
    Nivat.ColleReg.chainFull B vl u' b₀ 0 ⊆ Nivat.ColleReg.chainFull B vl u' b₀ k :=
  chainFull_mono B vl u' b₀ (Nat.zero_le k)

#print axioms Nivat.ChainFullMono.cut_mono
#print axioms Nivat.ChainFullMono.chainFull_mono
#print axioms Nivat.ChainFullMono.chainFull_zero_subset

/-- ⭐ **把 `ConeHbase.not_chainFull_subset_coneRegion` 的「某个 `k`」升成「`k₀` 以上全部 `k`」。**

障碍是**单边性**（`coneRegion` 只扫 `+vl`，`chainFull` 截的是 `±vl` 的 `wedgeFull`），不是层级，
所以「把 `k` 调大」救不了。单调性把这句话变成内核事实：`chainFull … k₀ ⊆ chainFull … k`
（`k₀ ≤ k`），故 `k` 档若含于 `coneRegion`，`k₀` 档也会含，与既有反例冲突。

⚠ 量词口径（别写成 `∀ k ≥ 1`）：`ConeHbase.not_chainFull_subset_coneRegion` 的 `k` 是
**存在量词**下的，所以这里只能把 `k₀` 一并存在化、结论说 `∀ k ≥ k₀`。该文件 `:198` 的 docstring
自述其见证取 `k = 1`，**若**如此则实际射程是 `∀ k ≥ 1`——但那是它的 docstring，不是本结论的
内核内容，故本签名不写 `1`。

⛔ `k < k₀` 档不在结论里，且不该在——`ChainConeFit.chainFull_zero_subset_coneRegion_of_argmax`
（`ChainConeFit.lean:52`）在额外前提下证的正是 `chainFull … 0 ⊆ coneRegion`。
⟹ `hbase_of_cone_halfStrip_of_hmono` 的 `hchain` binder **只在低档有希望，高档整段是死的**。 -/
theorem not_chainFull_subset_coneRegion_all :
    ∃ (B : Set (ℤ × ℤ)) (vl u' b₀ : ℤ × ℤ) (k₀ : ℕ),
      Nivat.det u' vl = 1 ∧ b₀ ∈ B ∧ B.Finite ∧
      ∀ k : ℕ, k₀ ≤ k →
        ¬ (Nivat.ColleReg.chainFull B vl u' b₀ k ⊆
            Nivat.ConeRegion.coneRegion B vl u') := by
  obtain ⟨B, vl, u', b₀, k₀, hdet, hb₀, hfin, hno⟩ :=
    Nivat.ConeHbase.not_chainFull_subset_coneRegion
  refine ⟨B, vl, u', b₀, k₀, hdet, hb₀, hfin, ?_⟩
  intro k hk hsub
  exact hno (fun z hz => hsub (chainFull_mono B vl u' b₀ hk hz))

#print axioms Nivat.ChainFullMono.not_chainFull_subset_coneRegion_all

end Nivat.ChainFullMono
