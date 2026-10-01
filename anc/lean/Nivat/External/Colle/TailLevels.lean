/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.L1Line0

/-!
# `htail` 的生产者：Figure 2 的两条半无穷边 ⟹ `u'`-尾

原文：`b3_colle2.txt:396-398`（Figure 2）＋ `:780`（`𝓡_{ι−1} = H_B(ℓ) + ℕ v⃗_{ℓ_{ι−1}}`）。

`WindowPlace.exists_tau_mem_cut`（`WindowPlace.lean:34-35`）要的 `htail` 是

```
∀ z : ℤ × ℤ, lev N ≤ dot m z → ∃ T : ℤ, ∀ t : ℤ, T ≤ t → t • u' + z ∈ Rinf
```

**注意量词是 `∀ z : ℤ × ℤ`（整个平面），不是 `∀ z ∈ Rinf`。** 这不是加强：`dot m u' = 0`
说明 `m` ⟂ `u'`，而 `(vl, u')` 是幺模基，所以 `dot m z` **就是** `z` 的 `vl`-坐标
（差一个正因子 `dot m vl`）。于是「`z` 的层 ≥ `lev N`」已经把 `z` 锁在一条 `u'`-方向的
直线上，该直线与 `Rinf` 的交由下面两条前提控制：

* `hray`：原文 `:396-398` Figure 2 的第一条半无穷边——`Rinf` 沿 `u'` 是向上闭的
  （`𝓡_{ι−1}` 的定义 `:780` 里 `t ∈ ℤ₊` 那一条，逐字）；
* `hlevel`：第二条半无穷边——每个 `≥ lev N` 的层都在 `Rinf` 里被取到
  （`:816` 的 `0 = d₀ < d₁ < ⋯` 是**已达到**的距离序列，逐字）。

两条合起来：`z` 与同层的 `z₀ ∈ Rinf` 只差一个 `u'`-倍数（`vl`-分量被层相等逼成 0），
沿 `hray` 走够多步即可。**`T` 取 `-C`，`C` 是那个 `u'`-倍数。**

⚠ `Rinf = wedgeFull B vl u'`（`L1RegionBuild.lean:230`，即 `B + ℤ•vl + ℕ•u'`）**不是**
链上的 `Rinf`：链上的塔底是 `coneRegion B vl u' = B + ℕvl + ℕu'`（`ConeRegion.lean:68`，
原文 `:780`），而 `RegionSteps.lean` 的 `hbase₁` 正是在 `coneRegion` 上陈述周期性。
把 `Rinf` 换成 `ℤ•vl` 版是**比原文强**（硬规矩 7），故本文件走 `hray`/`hlevel` 这条。
-/

namespace Nivat.TailLevels

open Nivat
open Nivat.LE2 (dot)

variable {Rinf : Set (ℤ × ℤ)} {m u' vl : ℤ × ℤ}

/-- 沿 `u'` 的前向射线：`hray` 迭代 `k` 次。 -/
theorem ray_nsmul (hray : ∀ z ∈ Rinf, z + u' ∈ Rinf) {z₀ : ℤ × ℤ} (hz₀ : z₀ ∈ Rinf) :
    ∀ k : ℕ, z₀ + (k : ℤ) • u' ∈ Rinf := by
  intro k
  induction k with
  | zero => simpa using hz₀
  | succ n ih =>
      have := hray _ ih
      have heq : z₀ + (n : ℤ) • u' + u' = z₀ + ((n + 1 : ℕ) : ℤ) • u' := by
        push_cast
        module
      rwa [heq] at this

/-- **`htail` 的生产者。**

原文：`b3_colle2.txt:396-398`（Figure 2 的两条半无穷边）＋ `:780`（`t ∈ ℤ₊`）。

逐个量词的对应：

* `hray`（`∀ z ∈ Rinf, z + u' ∈ Rinf`）= `:780` 的 `t ∈ ℤ₊`，即 `𝓡` 沿 `v⃗_{ℓ_{ι−1}}` 闭；
* `hlevel`（每层被取到）= Figure 2 里另一条半无穷边扫过所有层，也就是 `:816`
  「`0 = d₀ < d₁ < ⋯` 是已达到的距离」那句；
* `hmu' : dot m u' = 0` = 割线 `ℓ'` 沿 `u'`（`:816`）；
* `hmvl : 0 < dot m vl` = `m` 指向 `vl` 那一侧（层随 `vl` 上升）；
* `hunimod` = `(u', vl)` 是幺模基（`:766` 的循环序给出相邻两边行列式 ±1）。

结论里的 `∀ z : ℤ × ℤ` 之所以不是加强，见文件头。 -/
theorem htail_of_levels {lev : ℕ → ℤ} {N : ℕ}
    (hunimod : det u' vl = 1 ∨ det u' vl = -1)
    (hmu' : dot m u' = 0)
    (hmvl : 0 < dot m vl)
    (hray : ∀ z ∈ Rinf, z + u' ∈ Rinf)
    (hlevel : ∀ b : ℤ, lev N ≤ b → ∃ z₀ ∈ Rinf, dot m z₀ = b) :
    ∀ z : ℤ × ℤ, lev N ≤ dot m z →
      ∃ T : ℤ, ∀ t : ℤ, T ≤ t → t • u' + z ∈ Rinf := by
  intro z hz
  obtain ⟨z₀, hz₀, hlv⟩ := hlevel (dot m z) hz
  obtain ⟨A, C, hdec, -⟩ := Nivat.L1Line0.exists_decomp hunimod z₀ z
  -- 取 `dot m`：`dot m z = dot m z₀ + A * dot m vl + C * dot m u'`，而 `dot m u' = 0`。
  have hAzero : A = 0 := by
    have hmz : dot m z = dot m z₀ + A * dot m vl + C * dot m u' := by
      rw [hdec]
      simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [hmu', hlv] at hmz
    have : A * dot m vl = 0 := by omega
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · omega
  have hzC : z = z₀ + C • u' := by
    rw [hdec, hAzero]
    module
  refine ⟨-C, ?_⟩
  intro t ht
  have hk : 0 ≤ t + C := by omega
  have hray' := ray_nsmul hray hz₀ (t + C).toNat
  have hcast : ((t + C).toNat : ℤ) = t + C := Int.toNat_of_nonneg hk
  rw [hcast] at hray'
  have heq : z₀ + (t + C) • u' = t • u' + z := by
    rw [hzC]
    module
  rwa [heq] at hray'

end Nivat.TailLevels

#print axioms Nivat.TailLevels.ray_nsmul
#print axioms Nivat.TailLevels.htail_of_levels
