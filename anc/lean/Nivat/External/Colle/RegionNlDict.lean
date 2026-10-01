/-
Copyright (c) 2026 Nivat formalisation project. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges

/-!
# 归一化后的 `nℓ`/`vl`/`u'` 符号字典

`exists_preamble` 交出的 `(nℓ, vl)` 已被生产者归一化（`PROTOCOL.md §54 state 2`）：
除了 `dot nℓ vl = 0`，还带 `0 < det nℓ vl`，这条从第 183 轮起是
`exists_cutResidualR_of_claim46` 的 binder（`hdetpos`，`RegionSteps.lean:1920`）。

本文件把这条归一化的**全部算术后果**一次性写清楚。主结论：

```
nℓ = -(dir vl)   ∧   det u' vl = -1
```

⟹ `hunimod : det u' vl = 1 ∨ det u' vl = -1`（`RegionSteps.lean:1904`）与
`hprim : Prim nℓ`（`RegionSteps.lean:1913`）在归一化之后**都是推论，不必当 binder**。

## 推导

`hperp : dot nℓ vl = 0` 加 `Primitive vl`，经 `det (dir vl) nℓ = -(dot nℓ vl)`
把 `nℓ` 钉成 `dir vl` 的整数倍 `k`（`exists_smul_of_det_eq_zero`，`LatticeEdges.lean:122`）。
于是

* `det nℓ vl = -k‖vl‖²`，归一化的 `0 < det nℓ vl` 逼出 `k < 0`；
* `dot nℓ u' = -(k · det u' vl)`，`hnu : dot nℓ u' = -1` 给 `k · det u' vl = 1`；

两条合起来只剩 `k = -1`、`det u' vl = -1`。

⚠ **不是空真**：`u'` 在 `nℓ` 之后选，`hnu`（`RegionSteps.lean:1920`）是真实 binder。

⛔ **射程**：本文件只谈**链上**对象。`vl` 与原文 `v⃗_{ℓ_ι}` 的对齐尚未证出（第 181 轮的
带符号 `det` 硬闸），所以 `det u' vl = -1` **不许**被当成原文侧的取向结论搬到台架上，
反向亦然。

数值实例（硬规矩 6）：`nℓ = (1,0)`、`vl = (0,1)`、`u' = (-1,0)`——
`dot nℓ vl = 0`、`det nℓ vl = 1 > 0`、`dot nℓ u' = -1`，而 `det u' vl = -1`、`-(dir vl) = (1,0) = nℓ`。
见 `det_u'_numeric`。

来源：`tmp/wip/lane-towerpkg-region.lean` 的 `§10`（lane-towerpkg，第 179–183 轮）。
辅助引理全部 `private` 就地重证，只为免去为几条 `gcd` / `ring` 恒等式多拉 import。
-/

set_option autoImplicit false

namespace Nivat.RegionNlDict

open Nivat Nivat.LE2

/-! ## §1. 私有算术辅助 -/

private theorem prim_neg' {n : ℤ × ℤ} (h : Prim n) : Prim (-n) := by
  simpa only [Prim, Prod.fst_neg, Prod.snd_neg, Int.gcd, Int.natAbs_neg] using h

private theorem prim_dir' {n : ℤ × ℤ} (h : Prim n) : Prim (dir n) := by
  have h1 : Int.gcd (dir n).1 (dir n).2 = Nat.gcd n.2.natAbs n.1.natAbs := by
    simp [dir, Int.gcd]
  have h2 : Int.gcd n.1 n.2 = Nat.gcd n.1.natAbs n.2.natAbs := by simp [Int.gcd]
  show Int.gcd (dir n).1 (dir n).2 = 1
  rw [h1, Nat.gcd_comm, ← h2]
  exact h

/-- 无前提代数：`det (dir v) n = -(dot n v)`。把「`n ⊥ v`」翻成「`n ∥ dir v`」用的。 -/
private theorem det_dir_left_eq_neg_dot' (n v : ℤ × ℤ) : det (dir v) n = - dot n v := by
  simp only [det, dir, dot]; ring

private theorem sq_add_sq_pos' {v : ℤ × ℤ} (h : v ≠ 0) : 0 < v.1 * v.1 + v.2 * v.2 := by
  have hc : v.1 ≠ 0 ∨ v.2 ≠ 0 := by
    rcases eq_or_ne v.1 0 with h1 | h1
    · rcases eq_or_ne v.2 0 with h2 | h2
      · exact absurd (Prod.ext h1 h2) h
      · exact Or.inr h2
    · exact Or.inl h1
  rcases hc with h1 | h2
  · nlinarith [mul_self_nonneg v.2, mul_self_pos.mpr h1]
  · nlinarith [mul_self_nonneg v.1, mul_self_pos.mpr h2]

/-! ## §2. 字典 -/

/-- **归一化的符号字典。**  同时给出 `nℓ = -(dir vl)` 与 `det u' vl = -1`。

前提全部是 `exists_cutResidualR_of_claim46` 的现成 binder：
`hvl_prim`（`RegionSteps.lean:1905`）、`hperp`（`:1906`）、`hdetpos`（`:1920`）、`hnu`（`:1920`）。 -/
theorem nl_eq_neg_dir_vl_and_det_u' {nl vl u' : ℤ × ℤ}
    (hvlp : Primitive vl) (hperp : dot nl vl = 0) (hdet : 0 < det nl vl)
    (hnu : dot nl u' = -1) : nl = -(dir vl) ∧ det u' vl = -1 := by
  have hvp : Prim vl := prim_iff_primitive.mpr hvlp
  have hdz : det (dir vl) nl = 0 := by rw [det_dir_left_eq_neg_dot', hperp, neg_zero]
  obtain ⟨k, hk⟩ := exists_smul_of_det_eq_zero (prim_dir' hvp) hdz
  have hq : (0 : ℤ) < vl.1 * vl.1 + vl.2 * vl.2 := sq_add_sq_pos' hvp.ne_zero
  have hdetk : det nl vl = -(k * (vl.1 * vl.1 + vl.2 * vl.2)) := by
    rw [hk]; simp only [det, dir]; ring
  have hkneg : k < 0 := by
    rw [hdetk] at hdet
    by_contra hc
    have hk0 : (0 : ℤ) ≤ k := not_lt.mp hc
    nlinarith [mul_nonneg hk0 hq.le]
  have hnuk : dot nl u' = -(k * det u' vl) := by
    rw [hk]; simp only [dot, dir, det]; ring
  have hk1 : k * det u' vl = 1 := by
    have h := hnu
    rw [hnuk] at h
    linarith
  have hku : det u' vl < 0 := by
    by_contra hc
    have hge : (0 : ℤ) ≤ det u' vl := not_lt.mp hc
    nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ -k) hge]
  have hkm1 : k = -1 := by
    by_contra hne
    have hk2 : k ≤ -2 := by omega
    nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ -k - 2)
      (by omega : (0 : ℤ) ≤ -det u' vl - 1)]
  subst hkm1
  have hd : det u' vl = -1 := by linarith
  refine ⟨?_, hd⟩
  rw [hk]
  simp [Prod.ext_iff]

/-- **`hunimod` 的 `-1` 支，单独一条。**  这是 team-lead 第 183 轮 §3 裁决第 2 条要的东西：
`hunimod` 不在 `RegionSteps` 降，而是把 `det u' vl = -1` 做成独立引理供给
`TowerConstruct` / sortdir 一侧，用来塌掉 `nprevOf`（`TowerConstruct.lean:1074`）
定义里的 `if 0 < det u' (-vl)` 分支。

（注意 `det u' (-vl) = -det u' vl = 1 > 0`，所以塌掉的是 `then` 支。） -/
theorem det_u'_vl_eq_neg_one_of_normalized {nl vl u' : ℤ × ℤ}
    (hvlp : Primitive vl) (hperp : dot nl vl = 0) (hdet : 0 < det nl vl)
    (hnu : dot nl u' = -1) : det u' vl = -1 :=
  (nl_eq_neg_dir_vl_and_det_u' hvlp hperp hdet hnu).2

/-- 上一条的 `det u' (-vl)` 形状，直接对上 `nprevOf` 里那个 `if` 的判定式。 -/
theorem det_u'_neg_vl_pos_of_normalized {nl vl u' : ℤ × ℤ}
    (hvlp : Primitive vl) (hperp : dot nl vl = 0) (hdet : 0 < det nl vl)
    (hnu : dot nl u' = -1) : 0 < det u' (-vl) := by
  have h := det_u'_vl_eq_neg_one_of_normalized hvlp hperp hdet hnu
  have : det u' (-vl) = - det u' vl := by
    simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
  omega

/-- `hunimod`（`RegionSteps.lean:1904`）在归一化之后是推论，不必当 binder。 -/
theorem unimod_of_normalized {nl vl u' : ℤ × ℤ}
    (hvlp : Primitive vl) (hperp : dot nl vl = 0) (hdet : 0 < det nl vl)
    (hnu : dot nl u' = -1) : det u' vl = 1 ∨ det u' vl = -1 :=
  Or.inr (nl_eq_neg_dir_vl_and_det_u' hvlp hperp hdet hnu).2

/-- `hprim : Prim nℓ`（`RegionSteps.lean:1913`）同样是推论：`nℓ = -(dir vl)` 而 `dir vl` 本原。 -/
theorem prim_nl_of_normalized {nl vl u' : ℤ × ℤ}
    (hvlp : Primitive vl) (hperp : dot nl vl = 0) (hdet : 0 < det nl vl)
    (hnu : dot nl u' = -1) : Prim nl := by
  rw [(nl_eq_neg_dir_vl_and_det_u' hvlp hperp hdet hnu).1]
  exact prim_neg' (prim_dir' (prim_iff_primitive.mpr hvlp))

/-- 硬规矩 6 的数值实例：`nℓ = (1,0)`、`vl = (0,1)`、`u' = (-1,0)`。 -/
theorem det_u'_numeric :
    dot ((1, 0) : ℤ × ℤ) ((0, 1) : ℤ × ℤ) = 0 ∧
      0 < det ((1, 0) : ℤ × ℤ) ((0, 1) : ℤ × ℤ) ∧
      dot ((1, 0) : ℤ × ℤ) ((-1, 0) : ℤ × ℤ) = -1 ∧
      det ((-1, 0) : ℤ × ℤ) ((0, 1) : ℤ × ℤ) = -1 ∧
      -(dir ((0, 1) : ℤ × ℤ)) = ((1, 0) : ℤ × ℤ) := by decide

#print axioms nl_eq_neg_dir_vl_and_det_u'
#print axioms det_u'_vl_eq_neg_one_of_normalized
#print axioms det_u'_neg_vl_pos_of_normalized
#print axioms unimod_of_normalized
#print axioms prim_nl_of_normalized
#print axioms det_u'_numeric

end Nivat.RegionNlDict
