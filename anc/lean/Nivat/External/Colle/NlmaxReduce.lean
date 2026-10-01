/-
集成者，第 167 轮：**把 `hnlmax` 砍掉一半**（`RegionSteps.lean` 的 `exists_cutResidualR_of_claim46` 那条 `sorry` 的前置）。

## 为什么可以砍

`hnlmax : ∀ b ∈ 𝒮_φ, dot nℓ b ≤ dot nℓ a`（`RegionSteps.lean` 的 `exists_cutResidualR_of_claim46` 内）里的 `a` **不是原文的对象**。
原文 `scratch/b3_colle2.txt:806-870`（Claim 4.7 及其后）通篇没有引入任何点 `a`：那里只有
`ℛ_i`、`ℛ^n_I`、`N`、`h`、`𝒯`，以及 Figure 11(B) 的传播论证
（`:852`「Since `𝒮_φ` is η-generating, we get that `(T^uη)|ℛ^{N+1}_I = (T^h(T^uη))|ℛ^{N+1}_I`」）。

点 `a` 是**我们自己**造的：`RegionSteps.lean` 里 `L1GenPackage.exists_gen_package'` 的 `obtain`
（`grep -n "exists_gen_package'" Nivat/External/Colle/RegionSteps.lean`）按**字典序极值**取它
（先 `dot m` 极小，同层再按 `w` 方向极小），产出两条性质

```
ha_min : ∀ b ∈ 𝒮_φ, dot m a ≤ dot m b
ha_end : ∀ b ∈ 𝒮_φ, dot m b = dot m a → ∃ t : ℕ, b = a + t • w
```

⟹ 按硬规矩 5「被证伪时先问『哪个量词是我们加的』」：`a` 的定义性质是我们加的，
`hnlmax` 是在这个自造对象上**再要一条**。三条内核反例
（`hadj_does_not_imply_hwadj` / `all_premises_and_not_nlmax` / `minimality_does_not_force_hwadj`）
之所以都成立，根就在这里——不是几何证不出来，是这条要求本来就没有原文依据。

## 本文件做的事

`ha_end` 说「极小层里的点全是 `a + t•w`（`t : ℕ`）」，而 `hwneg : dot nℓ w < 0`（`RegionSteps.lean` 里 `exists_cutResidualR_of_claim46` 的塔包 `obtain`
分量，`grep -n "dot nℓ w < 0"`）说沿 `+w` 走 `dot nℓ` 严格下降。两条一拼，**`a` 在极小层上自动是 `dot nℓ` 的最大者**——白送。

⟹ `hnlmax` 等价于只在**严格更高层**上的那一半：

```
∀ b ∈ 𝒮_φ, dot m a < dot m b → dot nℓ b ≤ dot nℓ a
```

洞口从「`a` 同时极小化 `dot m`、极大化 `dot nℓ`」缩成「`dot m` 严格大的点 `dot nℓ` 不会更大」。
这不是把洞补上，是把它砍掉一半并指出剩下那半**确实需要 ξ 那一侧**
（`hξ` / `hgen` / `hgenφ` / `hbase` / `hinf`），与 `RegionSteps.lean` 里该 `sorry` 上方的升级结论一致。
-/
import Nivat.External.Colle.RegionCut

set_option autoImplicit false

namespace Nivat.NlmaxReduce

open Nivat Nivat.LE2

/-- **白送的那一半**：在 `dot m` 的极小层上，`a` 自动极大化 `dot nℓ`。

只用两条现成前提：`ha_end`（`exists_gen_package'` 的 `obtain` 分量，极小层里的点全是 `a + t•w`，`t : ℕ`）
与 `hwneg`（塔包 `obtain` 分量，`dot nℓ w < 0`）。`t : ℕ` 的非负性是承重的：
若允许 `t < 0` 则结论反向。 -/
theorem nlmax_on_min_level {Sφ : Finset (ℤ × ℤ)} {m w nl a : ℤ × ℤ}
    (hwneg : dot nl w < 0)
    (ha_end : ∀ b ∈ Sφ, dot m b = dot m a → ∃ t : ℕ, b = a + (t : ℤ) • w) :
    ∀ b ∈ Sφ, dot m b = dot m a → dot nl b ≤ dot nl a := by
  intro b hb hlev
  obtain ⟨t, rfl⟩ := ha_end b hb hlev
  rw [dot_add_zsmul]
  have ht : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
  nlinarith

/-- **`hnlmax` 的归约**：只欠严格更高层的那一半。

逐量词对应：结论 `∀ b ∈ 𝒮_φ, dot nℓ b ≤ dot nℓ a` 就是 `exists_cutResidualR_of_claim46` 的
`hnlmax`，一字不差；`ha_min` / `ha_end` 是 `exists_gen_package'` 那条 `obtain` 现成的；
`hwneg` 是塔包 `obtain` 的分量。
唯一新前提 `hstrict` 比 `hnlmax` **严格弱**——它只管 `dot m a < dot m b` 的那些 `b`。 -/
theorem nlmax_of_strict {Sφ : Finset (ℤ × ℤ)} {m w nl a : ℤ × ℤ}
    (hwneg : dot nl w < 0)
    (ha_min : ∀ b ∈ Sφ, dot m a ≤ dot m b)
    (ha_end : ∀ b ∈ Sφ, dot m b = dot m a → ∃ t : ℕ, b = a + (t : ℤ) • w)
    (hstrict : ∀ b ∈ Sφ, dot m a < dot m b → dot nl b ≤ dot nl a) :
    ∀ b ∈ Sφ, dot nl b ≤ dot nl a := by
  intro b hb
  rcases eq_or_lt_of_le (ha_min b hb) with heq | hlt
  · exact nlmax_on_min_level hwneg ha_end b hb heq.symm
  · exact hstrict b hb hlt

/-- 反向：`hnlmax` 当然蕴含 `hstrict`。合起来说明归约**没有丢信息**，
`hnlmax` 与 `hstrict` 在现成前提下等价。 -/
theorem strict_of_nlmax {Sφ : Finset (ℤ × ℤ)} {m nl a : ℤ × ℤ}
    (h : ∀ b ∈ Sφ, dot nl b ≤ dot nl a) :
    ∀ b ∈ Sφ, dot m a < dot m b → dot nl b ≤ dot nl a :=
  fun b hb _ => h b hb

/-- **接口引理**：`RegionSteps.lean:2201` 那条 `hstrict` sorry 的目标形状，
与「`a` 是 `𝒮_φ` 上 `dot nℓ` 的全局最大者」（`hnlmax`）在现成前提
（`ha_min`/`ha_end`/`hwneg`，同上）下**等价**。`⟹` 就是 `nlmax_of_strict`
（把 `hstrict` 升级成 `hnlmax`），`⟸` 就是 `strict_of_nlmax`（`hnlmax` 显然蕴含 `hstrict`，
丢掉多余的前提即可）。这是两个方向拼起来的纯打包，无新证明内容。

给判据侧（lane-towerpkg 的 `det` 版本、lane-tower-hlev 的扇序版本）的唯一接口：
只要判据侧能产出等价式右边（`∀ b ∈ 𝒮_φ, dot nℓ b ≤ dot nℓ a`），
经 `.mpr` 就是 `RegionSteps.lean:2201` 要的 `hstrict`。 -/
theorem hstrict_iff_nlmax {Sφ : Finset (ℤ × ℤ)} {m w nl a : ℤ × ℤ}
    (hwneg : dot nl w < 0)
    (ha_min : ∀ b ∈ Sφ, dot m a ≤ dot m b)
    (ha_end : ∀ b ∈ Sφ, dot m b = dot m a → ∃ t : ℕ, b = a + (t : ℤ) • w) :
    (∀ b ∈ Sφ, dot m a < dot m b → dot nl b ≤ dot nl a) ↔
      (∀ b ∈ Sφ, dot nl b ≤ dot nl a) :=
  ⟨nlmax_of_strict hwneg ha_min ha_end, strict_of_nlmax⟩

/-- **可选加固**：把 `hstrict` 升级成「`a` 同时是 `dot m` 的全局最小者
与 `dot nℓ` 的全局最大者」这一对偶极值刻画——判据侧若需要「`a ∈ argmin(dot m) ∩
argmax(dot nℓ)」形状的输入，直接由此产出，不必再拆 `hstrict_iff_nlmax`。 -/
theorem dual_extremum_of_strict {Sφ : Finset (ℤ × ℤ)} {m w nl a : ℤ × ℤ}
    (hwneg : dot nl w < 0)
    (ha_min : ∀ b ∈ Sφ, dot m a ≤ dot m b)
    (ha_end : ∀ b ∈ Sφ, dot m b = dot m a → ∃ t : ℕ, b = a + (t : ℤ) • w)
    (hstrict : ∀ b ∈ Sφ, dot m a < dot m b → dot nl b ≤ dot nl a) :
    (∀ b ∈ Sφ, dot m a ≤ dot m b) ∧ (∀ b ∈ Sφ, dot nl b ≤ dot nl a) :=
  ⟨ha_min, nlmax_of_strict hwneg ha_min ha_end hstrict⟩

end Nivat.NlmaxReduce

#print axioms Nivat.NlmaxReduce.nlmax_on_min_level
#print axioms Nivat.NlmaxReduce.nlmax_of_strict
#print axioms Nivat.NlmaxReduce.strict_of_nlmax
#print axioms Nivat.NlmaxReduce.hstrict_iff_nlmax
#print axioms Nivat.NlmaxReduce.dual_extremum_of_strict
