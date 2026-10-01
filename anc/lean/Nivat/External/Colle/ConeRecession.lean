/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.RecessionCone

/-!
# Two-ray recession: the full cone spanned by both semi-infinite edges

原文：`b3_colle2.txt:506`（`Â_∞` 带两条半无限边，一条平行 `ℓ`、一条平行 `ℓ_J`）以及
`:826-856`（Figure 11(B) 的「房间」）。

`RecessionCone.recession_of_ray` 只给**一条**射线方向上的封闭性。本文件把两条射线合成
**整个二维锥**：格凸区域 `R` 若在方向 `u`、`u'` 上都封闭，则 `R` 对锥
`{s·u + t·u' : s, t ≥ 0}` 里的**任意格点**封闭——包括那些**不是** `u`、`u'` 的 `ℕ`-组合的
格点（只有 `det u u' = ±1` 时才没有这种点，而 `Colle41.IsRegion` 只给 `det u u' ≠ 0`）。

关键是 Cramer 恒等式 `det u u' • x = (det x u') • u + (det u x) • u'`（`cramer_smul`）：
它把 `x` 的锥成员性化成两个行列式的符号条件，并把格点 `z + x` 放到 `z` 与
`z + (det u u') • x` 的**实线段**上；再由格凸性（`R = toReal ⁻¹' C`，`C` 凸）落回 `R`。
-/

set_option autoImplicit false

namespace Nivat.RecessionCone

open Nivat Nivat.LE2

private theorem toReal_add' (z w : ℤ × ℤ) : toReal (z + w) = toReal z + toReal w := by
  simp only [toReal, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Int.cast_add]

private theorem toReal_zsmul' (n : ℤ) (z : ℤ × ℤ) : toReal (n • z) = (n : ℝ) • toReal z := by
  simp only [toReal, Prod.smul_fst, Prod.smul_snd, Prod.smul_mk, smul_eq_mul, Int.cast_mul]

/-- 单方向封闭可迭代到任意 `ℕ` 倍。 -/
theorem add_nsmul_mem' {R : Set (ℤ × ℤ)} {u : ℤ × ℤ} (hu : ∀ z ∈ R, z + u ∈ R) :
    ∀ z ∈ R, ∀ n : ℕ, z + (n : ℤ) • u ∈ R := by
  intro z hz n
  induction n with
  | zero => simpa using hz
  | succ k ih =>
      have hstep := hu _ ih
      have e : z + (k : ℤ) • u + u = z + ((k + 1 : ℕ) : ℤ) • u := by push_cast; module
      rwa [e] at hstep

/-- 单方向封闭可迭代到任意非负 `ℤ` 倍。 -/
theorem add_zsmul_mem {R : Set (ℤ × ℤ)} {u : ℤ × ℤ} (hu : ∀ z ∈ R, z + u ∈ R)
    {z : ℤ × ℤ} (hz : z ∈ R) {n : ℤ} (hn : 0 ≤ n) : z + n • u ∈ R := by
  have hmem := add_nsmul_mem' hu z hz n.toNat
  rwa [Int.toNat_of_nonneg hn] at hmem

/-- **线段落回**：格凸区域里 `z` 与 `z + D • x` 都在，`D ≥ 1`，则中间的格点 `z + x` 也在。

`z + x` 在实线段上的参数是 `1 / D`，故 `C` 的凸性直接给出；再由 `R = toReal ⁻¹' C`
把实点拉回格点（这一步正是 `IsLatticeConvexRegion` 比「凸包交 `ℤ²` 的子集」强的地方）。 -/
theorem mem_of_zsmul_mem {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R)
    {z x : ℤ × ℤ} {D : ℤ} (hD : 0 < D) (hz : z ∈ R) (hDx : z + D • x ∈ R) :
    z + x ∈ R := by
  obtain ⟨C, hconv, _, hReq⟩ := hR
  rw [hReq] at hz hDx ⊢
  simp only [Set.mem_preimage] at hz hDx ⊢
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hDne : (D : ℝ) ≠ 0 := ne_of_gt hDR
  have hle : (1 : ℝ) / (D : ℝ) ≤ 1 := by
    rw [div_le_one hDR]; exact_mod_cast hD
  have hexp : toReal (z + D • x) = toReal z + (D : ℝ) • toReal x := by
    rw [toReal_add', toReal_zsmul']
  have hkey : ((1 : ℝ) - 1 / (D : ℝ)) • toReal z + ((1 : ℝ) / (D : ℝ)) • toReal (z + D • x)
      = toReal (z + x) := by
    rw [hexp, toReal_add', smul_add, smul_smul, one_div, inv_mul_cancel₀ hDne, one_smul]
    module
  rw [← hkey]
  exact hconv hz hDx (by linarith) (by positivity) (by ring)

/-- **Cramer 恒等式**（`ℤ²`，无需可逆性）：`det u u' • x = (det x u') • u + (det u x) • u'`. -/
theorem cramer_smul (u u' x : ℤ × ℤ) :
    det u u' • x = (det x u') • u + (det u x) • u' := by
  have h1 : (det u u' • x).1 = det u u' * x.1 := rfl
  have h2 : (det u u' • x).2 = det u u' * x.2 := rfl
  have h3 : ((det x u') • u + (det u x) • u').1 = det x u' * u.1 + det u x * u'.1 := rfl
  have h4 : ((det x u') • u + (det u x) • u').2 = det x u' * u.2 + det u x * u'.2 := rfl
  rw [Prod.ext_iff]
  refine ⟨?_, ?_⟩
  · rw [h1, h3]; simp only [det]; ring
  · rw [h2, h4]; simp only [det]; ring

/-- **两条射线张成的整锥**（本文件的目标）。

`R` 格凸、在 `u` 与 `u'` 两个方向上都封闭；`x` 落在实锥 `{s·u + t·u' : s,t ≥ 0}` 里
（用行列式表达：`det u u'` 与 `det x u'`、`det u x` 同号）。结论：`R` 对 `+x` 封闭。

符号条件的读法：记 `δ = det u u'`，则 `δ • x = P • u + Q • u'`，`P = det x u'`，`Q = det u x`，
即 `x = (P/δ)·u + (Q/δ)·u'`；`0 ≤ δ·P` 与 `0 ≤ δ·Q` 恰好是 `P/δ ≥ 0` 与 `Q/δ ≥ 0`。 -/
theorem mem_of_cone {R : Set (ℤ × ℤ)} (hR : IsLatticeConvexRegion R) {u u' : ℤ × ℤ}
    (hu : ∀ z ∈ R, z + u ∈ R) (hu' : ∀ z ∈ R, z + u' ∈ R)
    (hdet : det u u' ≠ 0) {z x : ℤ × ℤ} (hz : z ∈ R)
    (h1 : 0 ≤ det u u' * det x u') (h2 : 0 ≤ det u u' * det u x) :
    z + x ∈ R := by
  set δ : ℤ := det u u' with hδ
  set P : ℤ := det x u' with hP
  set Q : ℤ := det u x with hQ
  have hcramer : δ • x = P • u + Q • u' := cramer_smul u u' x
  -- 取 `D := |δ| > 0`，并把 `P`、`Q` 同步改写成非负系数。
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · -- `δ < 0`：`(-δ) • x = (-P) • u + (-Q) • u'`，三个系数都非负。
    have hPle : P ≤ 0 := by nlinarith
    have hQle : Q ≤ 0 := by nlinarith
    have hstep : z + (-δ) • x ∈ R := by
      have e : z + (-δ) • x = z + (-P) • u + (-Q) • u' := by
        have : (-δ) • x = (-P) • u + (-Q) • u' := by
          have := congrArg (fun y : ℤ × ℤ => (-1 : ℤ) • y) hcramer
          simpa [neg_smul, smul_add, smul_smul] using this
        rw [this]; module
      rw [e]
      exact add_zsmul_mem hu' (add_zsmul_mem hu hz (by omega)) (by omega)
    exact mem_of_zsmul_mem hR (by omega) hz hstep
  · -- `δ > 0`：直接用 `δ • x = P • u + Q • u'`。
    have hPge : 0 ≤ P := by nlinarith
    have hQge : 0 ≤ Q := by nlinarith
    have hstep : z + δ • x ∈ R := by
      have e : z + δ • x = z + P • u + Q • u' := by rw [hcramer]; module
      rw [e]
      exact add_zsmul_mem hu' (add_zsmul_mem hu hz hPge) hQge
    exact mem_of_zsmul_mem hR hpos hz hstep

/-- **Figure 11(B) 的「房间」，化归到 `Sφ` 的切锥条件**（`b3_colle2.txt:826-856`）。

消费者：`RegionSteps.lean` 的 `exists_cutResidualR_of_claim46` 里 `hcover` 处的 `hroom`。
给定 `Rinf` 的两条半无限边（`Colle41.IsRegion Rinf vl w` 的第二、三个分量拆开传入），
「房间」就只剩 `hcone`：`Sφ` 在角点 `a` 处朝上的每个方向都落在 `cone (vl, w)` 里。

⚠ `hcone` **不能**只从 `ha_min`/`ha_end`/`Sphi_conv`/中心对称推出：lane-B-roomray 的内核见证
`rayRoomSigCS_false` 给了 `Sφ = {(0,0),(1,-2)}`、`vl = (1,0)`、`w = (0,1)` 的反例
（`b - a` 的 `w`-分量为负）。真正缺的前提是 `Rinf` 被 `E(Sφ)` 包络（原文 `:506`、`:806-812`），
它把 `Rinf` 角点的边法向限制在 `E(Sφ)` 里。本引理只负责「有了 `hcone` 就有房间」这一步。 -/
theorem room_of_cone {Rinf : Set (ℤ × ℤ)} {vl w m a : ℤ × ℤ} {Sφ : Finset (ℤ × ℤ)}
    (hconv : IsLatticeConvexRegion Rinf)
    (hvl : ∀ z ∈ Rinf, z + vl ∈ Rinf) (hw : ∀ z ∈ Rinf, z + w ∈ Rinf)
    (hdet : det vl w ≠ 0)
    (hcone : ∀ b ∈ Sφ, 0 < dot m (b - a) →
      0 ≤ det vl w * det (b - a) w ∧ 0 ≤ det vl w * det vl (b - a)) :
    ∀ q ∈ Rinf, ∀ b ∈ Sφ, 0 < dot m (b - a) → q + (b - a) ∈ Rinf := by
  intro q hq b hb hpos
  exact mem_of_cone hconv hvl hw hdet hq (hcone b hb hpos).1 (hcone b hb hpos).2

end Nivat.RecessionCone

#print axioms Nivat.RecessionCone.mem_of_cone
#print axioms Nivat.RecessionCone.room_of_cone