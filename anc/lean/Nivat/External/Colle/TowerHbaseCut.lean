/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: lane-tower-hbase
-/
import Nivat.External.Colle.Oct8Bench
import Nivat.External.Colle.EscapeWSubset

/-!
# `Cut i`：oct8 台架上的「交集版」壳，及其 `Env` / 严格性 / `escapeW`

**落地依据**：team-lead 第 215 轮裁决——lane-leafa-shell 按 §16 不能 `import` 我的
`tmp/wip/lane-tower-hbase-cut.lean`，只能按常数**重定义** `CutX`，于是「`CutX` 就是
lane-tower-hbase 的 `Cut`」是**常数比对、不是内核事实**。本模块把 `Cut` 及整组结论
搬进主仓，两份收据才能在内核里合成。

`cutX i` 逐字符是 team-lead 第 213 轮给的那一行：

```
Cut i := ShellMink.shellInter (hatOf Ax kkx vlx i)
           (MaxEnv.shell (⋃ j, hatOf Ax kkx vlx j) vJ1x nJx 0 1) wfan
         ∩ {z | z + (kkx i : ℤ) • vlx ∈ Nivat.Colle35.halfStrip (Bx i) vlx}
```

即 `ε = 1`、`i₀ = 0`，模型是 `Nivat/External/Colle/Oct8Bench.lean`
（`Nivat.LaneTowerOct8.Sphi = oct8 0 1 2 4 3 3 1 0`，见 `coe_Sphi`）。

## 结论

* **NEW-1 真**：`envOf_cut` / `enveloped_cut`（`EnvOf` 与 `Enveloped` 两种写法都给）。
* **NEW-2 真**：`cut_not_subset_hatOf`，见证点 `(1,1)`（`one_one_mem_cut` +
  `one_one_not_mem_hatOf`），对**每个** `i` 成立。
* **`escapeW` 真**：`escapeW_cut` / `escapeW_into_cut` / `escapeW_cut_guarded`，
  经泛型的 `escapeW_of_not_subset` 从 NEW-2 直接来，**不**依赖任何手挑的逃逸点。
  ⚠ `escapeW_of_not_subset` **不在本文件**——它住在 `Nivat/External/Colle/EscapeWSubset.lean`
  （同一 namespace `Nivat.LaneTowerHbaseCut`，所以全限定名不变；本文件 `import` 它）。
  拆分依据是 team-lead 第 218 轮裁决：那条是**纯链侧**的，最终消费者是 `RegionSteps.lean`
  的 `escapeW` binder，而那一侧不该认识 `Ax` / `KK`；同模块会把整座八边形台架拖进它的
  传递闭包（工具盲区 2 同源）。

⟹ **oct8 对交集路线不构成障碍。**

## ⛔ 辖域（§54，引用本模块任何一条时必须整段带上）

1. **全部结论钉死 `ε = 1`**：`cutX` 体内写的是 `MaxEnv.shell … 0 1`，**没有 `ε` 参数**。
   原因是 `shell_eq` 只在 `ε = 1` 上证过。`ChainExhaustInter.lean` 的 binder 表里那些
   `∀ ε` 形状**未测**（不是「已证」也不是「为假」）。
2. `cut_eq` 的第七个常数是 `2 * KK i`，**不是**未取交那版 `shellInter_eq` 的 `4 * KK i - 1`。
   凡引用未取交版的负面结论（`not_fillCover_body` / `not_Hwin_oct8` / `not_Hstep_oct8` /
   `not_fillCoverConcl_oct8`）必须同时带「辖域停在 `shellInter`，对交集版一个字没说」。
3. 本模块**没有**证「交集路线正确」，也**没有**证链上的 `Env (Cut i)` 一般成立；
   只证了「在 `oct8 0 1 2 4 3 3 1 0` 这一个族上，这几条不为假」。
4. 台架参数**一个字都没动**：所有 `def` 全部引用 `Oct8Bench.lean` 的原件（§52，不调参）。
5. **一名多物**：`nJx` 全仓有 **11 个定义点、4 个不同的值**（第 218 轮实测，
   `grep -rnE '^\s*(def|abbrev) +nJx' Nivat/ tmp/`，分母 11）：

   | 值 | 定义点数 | 出处 |
   |---|---|---|
   | `(-1,0)` | 1 | **主仓** `Oct8Bench.lean:473`（本模块用的就是这个） |
   | `(0,1)` | 7 | 全在 `tmp/wip/`（cd-cw-fillcover-refute / escape-escapeW-refute / fillcover-genclosure / fillcover-hsteplocal-refute / leafa-gen-fillcover / leafa-gen-fillcover-inter / leafa-gen-nameprobe 两个探针各一） |
   | `(0,-1)` | 1 | `tmp/wip/lane-env-refute-wedge.lean:507` |
   | `(1,0)` | 1 | `tmp/wip/lane-env-shellenv-refute.lean:90` |

   **四个轴向全齐**，而主仓那个 `(-1,0)` 是**少数派**——按裸短名回忆几何时，「多数印象」
   指向的恰恰是错的那个。本组全部几何论断依赖 `dot u wfan` 的符号，法向转 90° 恰好把
   「冻住」与「扫走」对调，转 180° 则整体反号。
   ⚠ 编译层**撞不上**（lane-tower-hlev 第 218 轮逐个查过那 10 个重定义点有没有同时
   `import`/`open` `Oct8Bench`：8 个是 0 处，剩下 2 个是 gen 故意做成那个配置的探针本身）。
   ⟹ 风险**全在报告层**：工具永远不报，人按短名互相转述几何就错。
   本模块一律写全限定名 `Nivat.LaneTowerOct8.*`，读者也请勿凭裸短名回忆几何。
   同理 `Sphi`：主仓有**两个值不同的具体常量**——`Nivat.LaneTowerOct8.Sphi`（12 点八边形）
   与 `Nivat.Colle37.Counterexample.Sphi`（`{(0,0),(0,1)}`，2 点），
   另有 `Nivat.Colle35.DecompData.Sphi` / `Nivat.Colle37` 侧两个结构字段。本模块只用第一个。

## 机理（为什么取交之后又回到八边形族里）

`Nivat.LaneTowerOct8.shellInter_eq` 给出
`Sh i = oct8 1 (2K-1) (2K) (8K-1) (6K) (8K-1) (4K-1) 0`（`K = KK i = i+2`）。
半带条件在 `v⃗_ℓ = (1,1)` 方向上解出来，只剩**一条**新的线性不等式：`-z.2 ≤ 2K`
（`t ≥ 0` 与 `B_i` 的第 7 条 `-y ≤ K` 一起把 `t ≤ z.2 + 2K` 逼出来；`t ≥ 0` 要求
`z.2 + 2K ≥ 0`）。反过来取 `t := max z.1 0`（只可能是 `0` 或 `1`，因为 `Sh i` 里 `z.1 ≤ 1`）
就把 `B_i` 的八条全部满足。所以

```
Cut i = oct8 1 (2K-1) (2K) (8K-1) (6K) (8K-1) (2K) 0     -- cut_eq
```

只把 `Sh i` 的第 7 条从 `4K-1` 收紧到 `2K`，**仍在八边形族里** ⟹ `Nd8` 八条照算
（`nd8_cut`），`enveloped_oct8` 直接给 `Enveloped`。第 207 轮那个逃逸点
`e i = (-6K+2, -2K-1)` 正是在这里被切掉：它的 `-y = 2K+1 > 2K`（`escape_not_mem_cut`）。
⟹ 「`∩` 把那个见证直接切掉、第 207 轮那份反证对新包一个字都没说」是**内核事实**
（`escape_mem_shellInter` 仍在，见 `cut_ne_shellInter`）。

`Cut i ⊋ Â_i` 的机理同样是一条：`Â_i = oct8 0 (2K-1) (2K) (8K-1) (6K) (8K-1) (2K) 0`
（`hatOf_eq` / `Ahat`），与 `Cut i` **只差第 1 条** `x ≤ 0` vs `x ≤ 1` ⟹ 整条竖边
`{(1,y) : 1 ≤ y ≤ 2K-2}` 在 `Cut i` 里、不在 `Â_i` 里，取 `y = 1` 即见证。

⚠ 这与 `maxA_x`（`Oct8Bench.lean`，`IsMaxEnvIn` 的第三支）**不矛盾**：
`Nivat.Colle35.IsMaxEnvIn Env C A` 的极大性只对 `T ⊆ C` 生效（`ChainMax.lean`，
`IsMaxEnvIn`），而 `C = canonA … = Ax i`（`canonA_eq_Ax`），
`(1,1) + K•v⃗_ℓ = (K+1, K+1)` 的第一坐标 `K+1 > K = c₁(Ax i)` ⟹ 平移回去的见证点
**不在** `C` 里，极大性管不到它。

⚠ `c₁ = 1` 且**与 `K` 无关**是整条交集路线的唯一支点（lane-leafa-shell 的
`fillCover_cutX` / `not_genClosure_without_anchor` 都压在它上面）。
**改本模块任何一条常数之前必须先通知 lane-leafa-shell**：反向包含救不了他——
若哪条常数比他那版**大**，多出来的点回到未取交那版壳的处境，`u₇` 反例照打。

⚠ 措辞（lane-leafa-shell 第 215 轮订正）：**不要**写成「同一条机理一次杀 `u₇`、一次救 `u₁`」。
「极面 ≥2 格点 ⟹ `GenClosure` 抬不动那面墙」这条机理在 `u₁` 上**同样成立**。
救场的不是机理，是**底集**：

| 墙 | 机理（抬不动） | 底集并集够不够到目标 | 结果 |
|---|---|---|---|
| `u₇` | 成立 | 够不到（`4K₀−1 < 4K−1`） | 致命 |
| `u₁` | 同样成立 | **够到**（`c₁ = 1`，与 `K` 无关） | 无害 |

⟹ 参照系是「与**底集并集**比」，不是「与 `Â_i` 比」。

## 原文侧（`scratch/b3_colle2.txt:518` 的定义，`:520` 的两个包含；本轮亲读实测行号）

原文 `:518` 定义 `Â_i^{(ε)} := {g - t v⃗_{ℓ_{J+1}} ∈ Â_∞^{(ε)} : g ∈ Â_i, t ∈ ℤ_+}`，
`:520` 接着写「… is an $E(\mathcal{S}_{\varphi})$-enveloped set. Furthermore, one has
$B_i - k_i \vec v_\ell \subset \hat A_i^{(\epsilon)} \subset H_{B_i}(\boldsymbol\ell) - k_i
\vec v_\ell$」——**两个包含都是原文的断言，没有论证**。交集路线做的事是把**右**包含从
「断言」挪进「对象的定义」。左包含还在不在？在，而且免费：它等价于 `A_i ⊆ H_{B_i}(ℓ)`，
即 `subStrip`，由 `Nivat.Colle35.subStrip_of_max`（`ChainMax.lean`）从 `maxA` 白送。
`hatOf_subset_cut` 就是这条在本族上的实例（对每个 `i`）。
⟹ 交集路线**不**牺牲原文的左包含。
⚠ 这条只谈 `:520` 那两个包含，**不**谈 `ϑ` / `x̂_per` 的一致性子句（那是别的 binder）。
-/

set_option autoImplicit false

namespace Nivat.LaneTowerHbaseCut

open Nivat Nivat.LE2

open Nivat.LaneTowerOct8 (Ax Bx kkx vlx nJx vJ1x wfan KK px xperx oct8 Nd8 mem_oct8 mem_oct8'
  two_le_KK kkx_cast nd8_Sphi coe_Sphi shellInter_eq face_le2_Sphi enveloped_oct8
  escape_mem_shellInter)

/-! ## §1  `cutX i`，逐字符照 team-lead 第 213 轮那一行 -/

/-- `Cut i`：`shellSubStrip` 的**体**当作因子交进壳集合。`ε = 1`（体内 `shell … 0 1`，
无 `ε` 参数）。原文对应 `scratch/b3_colle2.txt:518` 的 `Â_i^{(ε)}`，右包含由定义兑现。 -/
def cutX (i : ℕ) : Set (ℤ × ℤ) :=
  ShellMink.shellInter (Nivat.Colle35.hatOf Ax kkx vlx i)
      (MaxEnv.shell (⋃ j, Nivat.Colle35.hatOf Ax kkx vlx j) vJ1x nJx 0 1) wfan ∩
    {z : ℤ × ℤ | z + (kkx i : ℤ) • vlx ∈ Nivat.Colle35.halfStrip (Bx i) vlx}

/-- ⭐ **交集又是同族的八边形**：只把第 7 条从 `4K-1` 收紧到 `2K`。

⚠ 这条是 lane-leafa-shell 那份 `CutX` 与本模块 `cutX` 之间的过户凭据：他按常数重定义的
`CutX` 与右端逐字相同 ⟹ `cutX i = CutX i` 从「常数比对」升级为内核事实。 -/
theorem cut_eq (i : ℕ) :
    cutX i = oct8 1 (2 * KK i - 1) (2 * KK i) (8 * KK i - 1) (6 * KK i) (8 * KK i - 1)
      (2 * KK i) 0 := by
  have hK := two_le_KK i
  have hc := kkx_cast i
  ext z
  rw [cutX, Set.mem_inter_iff, shellInter_eq, mem_oct8, mem_oct8, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6, -, h8⟩, b, hb, t, hbt⟩
    rw [Bx, Ax, mem_oct8] at hb
    have ht0 : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
    have hsnd : z.2 + KK i = b.2 + (t : ℤ) := by
      have h := congrArg Prod.snd hbt
      simpa only [vlx, Prod.snd_add, Prod.smul_snd, smul_eq_mul, mul_one, hc] using h
    exact ⟨h1, h2, h3, h4, h5, h6, by omega, h8⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    obtain ⟨T, hT0, hTx, hTcase⟩ :
        ∃ T : ℤ, 0 ≤ T ∧ z.1 ≤ T ∧ (T = z.1 ∨ T = 0) :=
      ⟨max z.1 0, le_max_right _ _, le_max_left _ _, max_choice _ _⟩
    have hct : ((T.toNat : ℕ) : ℤ) = T := Int.toNat_of_nonneg hT0
    refine ⟨⟨h1, h2, h3, h4, h5, h6, by omega, h8⟩,
      (z.1 + KK i - T, z.2 + KK i - T), ?_, T.toNat, ?_⟩
    · rw [Bx, Ax, mem_oct8']
      exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · simp only [vlx, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul, mul_one, hc, hct]
      constructor <;> omega

/-- `cut_eq` 右端那八个常数满足 `Nd8`（八边形族的良构条件）。 -/
theorem nd8_cut (i : ℕ) :
    Nd8 1 (2 * KK i - 1) (2 * KK i) (8 * KK i - 1) (6 * KK i) (8 * KK i - 1)
      (2 * KK i) 0 := by
  have h := two_le_KK i
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-! ## §2  NEW-1：交集仍然 `E(𝒮_φ)`-enveloped -/

/-- ⭐ **NEW-1 真**（`Enveloped` 写法）。`𝒮_φ` 指 `Nivat.LaneTowerOct8.Sphi`，
**不是** `Nivat.Colle37.Counterexample.Sphi`（见抬头辖域 5）。 -/
theorem enveloped_cut (i : ℕ) :
    Enveloped (↑Nivat.LaneTowerOct8.Sphi : Set (ℤ × ℤ)) (cutX i) := by
  rw [cut_eq, coe_Sphi]
  exact enveloped_oct8 nd8_Sphi (nd8_cut i) face_le2_Sphi

/-- ⭐ **NEW-1 真**（`EnvOf` 写法，即 binder 表里 `Env` 在 `hEnv : Env = EnvOf ↑S` 下的形状；
`ChainExhaustInter.lean` 的 `escapeW` / `shellSubStrip` / `shellEnv` / `fillCover` 四条
守卫前提都是这个形状）。 -/
theorem envOf_cut (i : ℕ) :
    EnvOf (↑Nivat.LaneTowerOct8.Sphi : Set (ℤ × ℤ)) (cutX i) := by
  rw [EnvOf]; exact enveloped_cut i

/-! ## §3  NEW-2：严格性，见证点 `(1,1)` -/

/-- ⭐ **具名导出**（lane-leafa-shell 的接口条件之二 `h11 : ∀ i₀, (1,1) ∈ Cut i₀`，逐字）：
他的 `fillCover_of_subset_cutX` 第二条 binder 就是它，具名之后一行 `exact` 接上，
不必在他那边从 `cut_eq` 现推。 -/
theorem one_one_mem_cut (i : ℕ) : ((1 : ℤ), (1 : ℤ)) ∈ cutX i := by
  have h := two_le_KK i
  rw [cut_eq, mem_oct8']
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- `(1,1)` 不在 `Â_i` 里：`Â_i` 的第 1 条是 `x ≤ 0`。 -/
theorem one_one_not_mem_hatOf (i : ℕ) :
    ((1 : ℤ), (1 : ℤ)) ∉ Nivat.Colle35.hatOf Ax kkx vlx i := by
  rw [Nivat.LaneTowerOct8.hatOf_eq, Nivat.LaneTowerOct8.Ahat, mem_oct8']
  rintro ⟨h1, -⟩
  omega

/-- ⭐ **NEW-2 真**，对每个 `i`。 -/
theorem cut_not_subset_hatOf (i : ℕ) :
    ¬ (cutX i ⊆ Nivat.Colle35.hatOf Ax kkx vlx i) :=
  fun h => one_one_not_mem_hatOf i (h (one_one_mem_cut i))

/-- 原文 `scratch/b3_colle2.txt:520` 的**左**包含 `B_i - k_i v⃗_ℓ ⊂ Â_i^{(ε)}` 在本族上的实例
（`Bx = Ax` ⟹ 左边就是 `Â_i`）。交集没有牺牲它。 -/
theorem hatOf_subset_cut (i : ℕ) :
    Nivat.Colle35.hatOf Ax kkx vlx i ⊆ cutX i := by
  intro z hz
  have h := two_le_KK i
  rw [Nivat.LaneTowerOct8.hatOf_eq, Nivat.LaneTowerOct8.Ahat, mem_oct8] at hz
  rw [cut_eq, mem_oct8]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hz
  exact ⟨by omega, h2, h3, h4, h5, h6, h7, h8⟩

/-! ## §4  第 207 轮那个逃逸点确实被切掉了（§54） -/

/-- 第 207 轮的逃逸点 `e i = (-6K+2, -2K-1)` 不在 `cutX i` 里：它的 `-y = 2K+1 > 2K`。 -/
theorem escape_not_mem_cut (i : ℕ) :
    ((-6 * KK i + 2 : ℤ), (-2 * KK i - 1 : ℤ)) ∉ cutX i := by
  have h := two_le_KK i
  rw [cut_eq, mem_oct8']
  rintro ⟨-, -, -, -, -, -, h7, -⟩
  omega

/-- `Cut i` **真**比 `Sh i` 小：逃逸点在 `Sh i` 里、不在 `Cut i` 里。⟹ 交集不是恒等，
第 207 轮那份反证的见证被 `∩` 切掉，对新包无话可说。 -/
theorem cut_ne_shellInter (i : ℕ) :
    ¬ (ShellMink.shellInter (Nivat.Colle35.hatOf Ax kkx vlx i)
        (MaxEnv.shell (⋃ j, Nivat.Colle35.hatOf Ax kkx vlx j) vJ1x nJx 0 1) wfan ⊆ cutX i) :=
  fun h => escape_not_mem_cut i (h (escape_mem_shellInter i))

/-! ## §5  `hp_per` 一侧：换 `p` 没有出路

`Nivat.LaneTowerOct8.px_not_mem_Per_xperx`（`Oct8Bench.lean`，第 214 轮已落）给出
`px ∉ Per xperx` 的内核见证；本节把它推广到**任何**满足 `hdet` / `dot_nJ_p` 的 `p`。 -/

/-- `hdet` + `dot_nJ_p` + `rec_p` 在本族上把 `p` 逼成 `(a,a)`、`a < 0`；**任何**这样的 `p`
都不是 `xperx` 的周期。⟹ 想让 `Oct8Bench` 兑现 `hp_per`，换 `p` 是没有出路的。

逐条：`det p vlx = 0` ⟺ `p.1 = p.2`（`Nivat.LaneTowerOct8.vlx = (1,1)`）；
`dot nJx p ≠ 0` ⟺ `p.1 ≠ 0`（`Nivat.LaneTowerOct8.nJx = (-1,0)`——⚠ 不是 tmp 各台架
多数派的 `(0,1)`，差 90°）；周期性在 `z := (-p.1, 0)` 处撞车。
⚠ `rec_p` 给的 `a < 0`（而不只是 `a ≠ 0`）这里用不上，所以结论比需要的更强一点。
⚠ 本节**不**主张这个漏洞能不能补；只记边界：要救那份反证必须换 `xper`，不是换 `p`。
换 `xper` 会牵动 `canonA_eq_Ax` / `hnotDP_x` / `period_fst_zero` 三条，**未做**，
也不主张它易或难（§51）。 -/
theorem px_shape_not_per {p : ℤ × ℤ} (hdet : det p vlx = 0) (hdotp : dot nJx p ≠ 0) :
    p ∉ Per xperx := by
  have heq : p.1 = p.2 := by
    simp only [det, vlx] at hdet
    omega
  have hne : p.1 ≠ 0 := by
    simp only [dot, nJx] at hdotp
    omega
  intro hmem
  have h1 : xperx (((-p.1 : ℤ), (0 : ℤ)) + p) = xperx ((-p.1 : ℤ), (0 : ℤ)) :=
    congrFun (Nivat.mem_Per_iff.mp hmem) _
  have h2 : xperx (((-p.1 : ℤ), (0 : ℤ)) + p) := by
    show (((-p.1 : ℤ), (0 : ℤ)) + p).1 = 0
    show (-p.1 : ℤ) + p.1 = 0
    omega
  have h3 : xperx ((-p.1 : ℤ), (0 : ℤ)) := (iff_of_eq h1).mp h2
  have h4 : (-p.1 : ℤ) = 0 := h3
  omega

/-! ## §5b  NEW-2 为真**不**与 lane-leafa-shell 的 `cut_subset_hatOf` 冲突

他那条从极大性推出 `Cut ⊆ Â_i`，但**带着**一条前提
`hagree : ∀ z ∈ Sh i ε, η (z + (k_i v⃗_ℓ + u_i)) = x_per (z + k_i v⃗_ℓ)`
——「整个壳上都与 `x̂_per` 一致」。这条**不在** `ofPartsExhaustsInter` 的 binder 表里
（表里只有 `maxA` 那条经由 `canonA` 的一致性子句，管的是 `canonA` 内部）。

本节把它钉死：在 oct8 上 `hagree` **为假**，见证就是 NEW-2 的同一个点 `(1,1)`。
`(1,1) + k_i v⃗_ℓ = (K+1, K+1)` 在半带里（`w_mem_halfStrip`）却不在 `A_i` 里
（第一坐标 `K+1 > K = c₁`），而 `etax` 的构造是 `(w ∈ A_i) ↔ (w.1 = 0)`：两边都假 ⟹ 取值真；
`x_per (K+1,K+1)` 假 ⟹ 两者不等。

⟹ 正确读法：**oct8 否掉的是他那条的前提 `hagree`，不是他的定理。**
⟹ 交集路线在链上要的那对矛盾（极大性给 `⊆`、逃逸给 `⊄`）本族给不出；
本族只给出「`⊄` 那一半在 `hagree` 不成立时可以单独成立」。 -/

/-- `(1,1) + k_i v⃗_ℓ` 落在半带 `H_{B_i}(ℓ)` 里（取 `b = (K,K)`、`t = 1`）。 -/
theorem w_mem_halfStrip (i : ℕ) :
    (((1 : ℤ), (1 : ℤ)) + (kkx i : ℤ) • vlx) ∈ Nivat.Colle35.halfStrip (Bx i) vlx := by
  have hK := two_le_KK i
  have hc := kkx_cast i
  refine ⟨(KK i, KK i), ?_, 1, ?_⟩
  · rw [Bx, Ax, mem_oct8']
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · simp only [vlx, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, mul_one, hc, Nat.cast_one]
    constructor <;> omega

/-- ⭐ oct8 上 `hagree` 为假（对每个 `i`）。 -/
theorem not_hagree_x (i : ℕ) :
    ¬ (∀ z ∈ ShellMink.shellInter (Nivat.Colle35.hatOf Ax kkx vlx i)
          (MaxEnv.shell (⋃ j, Nivat.Colle35.hatOf Ax kkx vlx j) vJ1x nJx 0 1) wfan,
        Nivat.LaneTowerOct8.etax (z + ((kkx i : ℤ) • vlx + Nivat.LaneTowerOct8.ux i))
          = xperx (z + (kkx i : ℤ) • vlx)) := by
  intro h
  have hK := two_le_KK i
  have hc := kkx_cast i
  have heq := h _ (one_one_mem_cut i).1
  rw [← add_assoc] at heq
  have hnot0 : ¬ ((((1 : ℤ), (1 : ℤ)) + (kkx i : ℤ) • vlx).1 = 0) := by
    simp only [vlx, Prod.fst_add, Prod.smul_fst, smul_eq_mul, mul_one, hc]
    omega
  have hnotA : (((1 : ℤ), (1 : ℤ)) + (kkx i : ℤ) • vlx) ∉ Ax i := by
    rw [Ax, mem_oct8]
    simp only [vlx, Prod.fst_add, Prod.smul_fst, smul_eq_mul, mul_one, hc]
    rintro ⟨h1, -⟩
    omega
  have hetax : Nivat.LaneTowerOct8.etax
      ((((1 : ℤ), (1 : ℤ)) + (kkx i : ℤ) • vlx) + Nivat.LaneTowerOct8.ux i) :=
    (Nivat.LaneTowerOct8.etax_at (w_mem_halfStrip i)).mpr (iff_of_false hnotA hnot0)
  exact hnot0 ((iff_of_eq heq).mp hetax)

/-! ## §6  `escapeW`

逐字读 `ChainExhaustInter.lean` 的 `escapeW` binder（**按标识符名定位，不写行号**——
该文件的 docstring 长度反复变动，历史上的数字锚点已大面积作废），它的结论是**存在**式：

```
∀ ε i₀ : ℕ, 0 < ε → (∀ i, i₀ ≤ i → Env (shellInter …)) →
  ∀ i, max i₀ I₀ ≤ i → ∃ g ∈ hatOf A kk vl i, ∃ t : ℕ,
    g + (t : ℤ) • w ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε ∧
    g + (t : ℤ) • w ∉ hatOf A kk vl i
```

⟹ 它要的是**能逃逸**。所以 `escape_not_mem_cut`（§4）确实在「坏消息」那个方向上，
**但它不致命**：它只切掉第 207 轮那**一个**见证点，而 `escapeW` 只要**某一个**。

**判决：真**，而且不是靠另找一个巧点——`escapeW` 在交集路线上**根本不是独立义务**，
它是 NEW-2（`cut_not_subset_hatOf`）的推论。机理一行：`escapeW` 的结论
`∃ g ∈ Â_i, ∃ t, g + t•w ∈ Ainf ∧ ∉ Â_i` 逐字等于「`reachSet Â_i w ∩ Ainf` 有一个点不在
`Â_i` 里」，即 `¬ (shellInter Â_i Ainf w ⊆ Â_i)`。任何 `C ⊆ shellInter Â_i Ainf w` 的
严格性都蕴含它。

⚠ 辖域：本节证的是 `ε = 1` 那一格。binder 的 `∀ ε` 形状**没覆盖**。
`i` 给的是 `∀ i`，比 `max i₀ I₀ ≤ i` 强，那一侧不欠。 -/

/-- `Cut i ⊆ Sh i`，按 `cutX` 的定义（左因子）。 -/
theorem cut_subset_shellInter (i : ℕ) :
    cutX i ⊆ ShellMink.shellInter (Nivat.Colle35.hatOf Ax kkx vlx i)
      (MaxEnv.shell (⋃ j, Nivat.Colle35.hatOf Ax kkx vlx j) vJ1x nJx 0 1) wfan := by
  intro z hz
  exact hz.1

/-- ⭐ **`escapeW` 在 `Cut i` 上为真**（`ε = 1`，对**每个** `i`），逐字符照
`ChainExhaustInter.lean` 的 `escapeW` binder 的结论。经 `escapeW_of_not_subset` 从 §3 的
严格性来，**不**依赖第 207 轮那个被切掉的逃逸点。 -/
theorem escapeW_cut (i : ℕ) :
    ∃ g ∈ Nivat.Colle35.hatOf Ax kkx vlx i, ∃ t : ℕ,
      g + (t : ℤ) • wfan ∈
        MaxEnv.shell (⋃ j, Nivat.Colle35.hatOf Ax kkx vlx j) vJ1x nJx 0 1 ∧
      g + (t : ℤ) • wfan ∉ Nivat.Colle35.hatOf Ax kkx vlx i :=
  escapeW_of_not_subset (cut_subset_shellInter i) (cut_not_subset_hatOf i)

/-- 加强版：逃逸点不只落在壳里，它就落在 `Cut i` 里。见证是 §3 的 `(1,1)`；
`g` / `t` 由 `reachSet` 的存在量词直接给出，不用手算。 -/
theorem escapeW_into_cut (i : ℕ) :
    ∃ g ∈ Nivat.Colle35.hatOf Ax kkx vlx i, ∃ t : ℕ,
      g + (t : ℤ) • wfan ∈ cutX i ∧
      g + (t : ℤ) • wfan ∉ Nivat.Colle35.hatOf Ax kkx vlx i := by
  have h11 : ((1 : ℤ), (1 : ℤ)) ∈ ShellMink.shellInter (Nivat.Colle35.hatOf Ax kkx vlx i)
      (MaxEnv.shell (⋃ j, Nivat.Colle35.hatOf Ax kkx vlx j) vJ1x nJx 0 1) wfan :=
    cut_subset_shellInter i (one_one_mem_cut i)
  obtain ⟨g, hg, t, hzeq⟩ := h11.1
  refine ⟨g, hg, t, ?_, ?_⟩
  · rw [← hzeq]; exact one_one_mem_cut i
  · rw [← hzeq]; exact one_one_not_mem_hatOf i

/-- `escapeW` 的守卫前提在本族上也兑现得了（`Env (Cut i)`，§2），所以上面两条不是
空转：守卫真、结论真（§41）。 -/
theorem escapeW_cut_guarded (i : ℕ) :
    EnvOf (↑Nivat.LaneTowerOct8.Sphi : Set (ℤ × ℤ)) (cutX i) ∧
    (∃ g ∈ Nivat.Colle35.hatOf Ax kkx vlx i, ∃ t : ℕ,
      g + (t : ℤ) • wfan ∈ cutX i ∧
      g + (t : ℤ) • wfan ∉ Nivat.Colle35.hatOf Ax kkx vlx i) :=
  ⟨envOf_cut i, escapeW_into_cut i⟩

/-! ## §7  交付：逐字符展开（不经 `cutX` 这个缩写） -/

/-- ⭐ **交付**：`ε = 1`、`i₀ = 0`、`oct8 0 1 2 4 3 3 1 0` 参数**未改**，
交集版的两条新 binder 在**每个** `i` 上都成立。

⚠ 辖域（§54）：这是关于**这一个族**的陈述。它说的是「oct8 不再是交集路线的障碍」，
**不是**「交集路线的 `Env` 一般成立」。第三合取记录第 207 轮的逃逸点被切掉，
所以第一合取不是空真地绕过它（§41）。第四合取是原文 `:520` 的左包含。 -/
theorem cut_env_and_strict :
    (∀ i : ℕ, EnvOf (↑Nivat.LaneTowerOct8.Sphi : Set (ℤ × ℤ))
        (ShellMink.shellInter (Nivat.Colle35.hatOf Ax kkx vlx i)
            (MaxEnv.shell (⋃ j, Nivat.Colle35.hatOf Ax kkx vlx j) vJ1x nJx 0 1) wfan ∩
          {z : ℤ × ℤ | z + (kkx i : ℤ) • vlx ∈
            Nivat.Colle35.halfStrip (Bx i) vlx})) ∧
    (∀ i : ℕ, ¬ (ShellMink.shellInter (Nivat.Colle35.hatOf Ax kkx vlx i)
            (MaxEnv.shell (⋃ j, Nivat.Colle35.hatOf Ax kkx vlx j) vJ1x nJx 0 1) wfan ∩
          {z : ℤ × ℤ | z + (kkx i : ℤ) • vlx ∈
            Nivat.Colle35.halfStrip (Bx i) vlx} ⊆
        Nivat.Colle35.hatOf Ax kkx vlx i)) ∧
    (∀ i : ℕ, ¬ (ShellMink.shellInter (Nivat.Colle35.hatOf Ax kkx vlx i)
            (MaxEnv.shell (⋃ j, Nivat.Colle35.hatOf Ax kkx vlx j) vJ1x nJx 0 1) wfan ⊆
          ShellMink.shellInter (Nivat.Colle35.hatOf Ax kkx vlx i)
            (MaxEnv.shell (⋃ j, Nivat.Colle35.hatOf Ax kkx vlx j) vJ1x nJx 0 1) wfan ∩
          {z : ℤ × ℤ | z + (kkx i : ℤ) • vlx ∈
            Nivat.Colle35.halfStrip (Bx i) vlx})) ∧
    (∀ i : ℕ, Nivat.Colle35.hatOf Ax kkx vlx i ⊆
        ShellMink.shellInter (Nivat.Colle35.hatOf Ax kkx vlx i)
            (MaxEnv.shell (⋃ j, Nivat.Colle35.hatOf Ax kkx vlx j) vJ1x nJx 0 1) wfan ∩
          {z : ℤ × ℤ | z + (kkx i : ℤ) • vlx ∈
            Nivat.Colle35.halfStrip (Bx i) vlx}) ∧
    px ∉ Per xperx :=
  ⟨envOf_cut, cut_not_subset_hatOf, cut_ne_shellInter, hatOf_subset_cut,
    Nivat.LaneTowerOct8.px_not_mem_Per_xperx⟩

/-! ## §8  接线：`shellSubStrip` 在手时，`shellInter` 与 `cutX` 形的对象可互换

lane-leafa-gen 第 230 轮的裁决请求：链上字段（`ChainPartsFeed.lean:271-279 fillCover`）要的对象是
`shellInter …`，而本文件的台架谈的是 `cutX i = shellInter … ∩ {带体}`。两者的落差**恰好**是
`ChainPartsFeed.lean:257-263 shellSubStrip` 那一条 binder 的结论：

```
shellSubStrip : ∀ i, shellInter (hatOf A kk vl i) Ainf w ⊆
    {z | z + (kk i : ℤ) • vl ∈ halfStrip (B i) vl}
```

⟹ 有那条字段在手时，`U ⊆ body` 成立，于是 `U = U ∩ body`（`inter_body_eq`），两个方向的包含
都可以免费搬（`subset_of_inter_body` / `inter_body_subset_of_subset`）。下面三条把这一步写成
与 `U` / `body` 无关的集合论引理，**不**引入任何新 import。

⛔ **辖域（§54）**：本节只说「**在 `shellSubStrip` 成立的前提下**两者可互换」。本文件的 oct8
台架上那条前提**为假** —— `cut_env_and_strict` 的第三合取正是它的反面。所以这三条对台架的
反例结论没有影响，也不把台架变成正面见证。⚠ 另外全文件钉在 `ε = 1`（见 §6 开头），
链上字段是 `∀ ε`。

⛔⛔ **这三条在链上是恒等操作，不是减债项**（lane-leafa-gen 2026-09-25 内核核实，
`lane-leafa-gen-collarbody.lean` 的 `collarY_is_shellSubStrip` / `collarY_inter_body_eq` /
`hwin_inter_iff`，按标识符名查）：链上 `collarY` 与 `shellSubStrip` 字段的左端是**定义相等**，
于是 `collar ∩ body = collar`，换对象前后 `Hwin` 逐字等价 —— **两侧同强**。
⟹ 完整的账是：链上两个对象**相等**（桥通但无收益），台架上两个对象**严格不等**而桥的前件
恰好为假（拿不到 `hsub`，桥不通）。**两个对象只在 `shellSubStrip` 为假处分开，而正好在那里桥不通。**
⛔ 因此**不准**把本节当成「把债搬轻了」来引；它的用途只是省掉调用点的一次手工改写。
⚠ gen 的 EXIT／公理我未复核（§55）；我复核的是这段话与本节三条签名不矛盾。 -/

/-- `U ⊆ body ⟹ U = U ∩ body`。`shellSubStrip` 在手时把 `shellInter` 改写成 `cutX` 形。 -/
theorem inter_body_eq {U body : Set (ℤ × ℤ)} (hsub : U ⊆ body) : U = U ∩ body :=
  (Set.inter_eq_self_of_subset_left hsub).symm

/-- 从 `cutX` 形的包含回到 `shellInter` 形的包含（需要 `shellSubStrip`）。 -/
theorem subset_of_inter_body {U body T : Set (ℤ × ℤ)}
    (hsub : U ⊆ body) (h : U ∩ body ⊆ T) : U ⊆ T :=
  fun _ hz => h ⟨hz, hsub hz⟩

/-- 从 `shellInter` 形的包含到 `cutX` 形的包含（这一向**不**需要 `shellSubStrip`）。 -/
theorem inter_body_subset_of_subset {U body T : Set (ℤ × ℤ)}
    (h : U ⊆ T) : U ∩ body ⊆ T :=
  fun _ hz => h hz.1

end Nivat.LaneTowerHbaseCut

#print axioms Nivat.LaneTowerHbaseCut.cutX
#print axioms Nivat.LaneTowerHbaseCut.cut_eq
#print axioms Nivat.LaneTowerHbaseCut.nd8_cut
#print axioms Nivat.LaneTowerHbaseCut.enveloped_cut
#print axioms Nivat.LaneTowerHbaseCut.envOf_cut
#print axioms Nivat.LaneTowerHbaseCut.one_one_mem_cut
#print axioms Nivat.LaneTowerHbaseCut.one_one_not_mem_hatOf
#print axioms Nivat.LaneTowerHbaseCut.cut_not_subset_hatOf
#print axioms Nivat.LaneTowerHbaseCut.hatOf_subset_cut
#print axioms Nivat.LaneTowerHbaseCut.escape_not_mem_cut
#print axioms Nivat.LaneTowerHbaseCut.cut_ne_shellInter
#print axioms Nivat.LaneTowerHbaseCut.px_shape_not_per
#print axioms Nivat.LaneTowerHbaseCut.w_mem_halfStrip
#print axioms Nivat.LaneTowerHbaseCut.not_hagree_x
#print axioms Nivat.LaneTowerHbaseCut.cut_subset_shellInter
#print axioms Nivat.LaneTowerHbaseCut.escapeW_cut
#print axioms Nivat.LaneTowerHbaseCut.escapeW_into_cut
#print axioms Nivat.LaneTowerHbaseCut.escapeW_cut_guarded
#print axioms Nivat.LaneTowerHbaseCut.cut_env_and_strict
#print axioms Nivat.LaneTowerHbaseCut.inter_body_eq
#print axioms Nivat.LaneTowerHbaseCut.subset_of_inter_body
#print axioms Nivat.LaneTowerHbaseCut.inter_body_subset_of_subset
