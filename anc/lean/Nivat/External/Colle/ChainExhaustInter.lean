/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ChainAssembleInter
import Nivat.External.Colle.ItemII

/-!
# `ChainDataGeom.ofPartsInter` with its `ℓ_ι` side discharged by exhaustion

Lane `lane-shell`, 2026-09-22.  Mirrors `ChainExhaust.lean`'s `ChainDataGeom.ofPartsExhausts`
(which wraps `ofParts`) for `ChainDataGeom.ofPartsInter` (`ChainAssembleInter.lean`, the
`shellInter`-based instantiation).  Nothing in `ell_side_of_exhausts` / `rec_vJ_of_bottom` /
`latticeConvex_iUnion_hatOf` (`ItemII.lean`, `ChainAssemble.lean`) reads the `shell` field's
formula — they only use `hsweep hhp hswept bottom hEnv maxA hfin AhatMono`, all of which
`ofPartsInter` still takes unchanged — so the wiring is verbatim the same as
`ofPartsExhausts`, with the shell-group binders swapped for `ofPartsInter`'s (`w hsweepW
escapeW` in place of `escape`, `shellSubStrip`/`shellEnv`/`fillCover` restated against
`shellInter`). -/

set_option autoImplicit false

namespace Nivat.Colle35

open Nivat Nivat.LE2 Nivat.MaxEnv Nivat.ChainAsm

variable {α : Type*}

/-- **`ofPartsInter` with the `ℓ_ι` side supplied by `ell_side_of_exhausts`.**  Same binders as
`ChainDataGeom.ofPartsInter` up to `dot_nJ_p`; then `hEnv : Env = EnvOf ↑S` in place of `rec_vJ`
(matching `ofPartsExhausts`'s 2026-09-19 swap); then the exhaustion data instead of
`cL / ahat_halfPlane_L / ahat_attained_L / nfp_L`.

**`escapeW` 站在反证的哪一端（2026-09-24 裁决，`PROTOCOL.md §43`）.**
`scratch/b3_colle2.txt:512-530` 整段是一个反证：`:516` 逐字「suppose, by contradiction, that
`ϑ|Â_∞^{(ε)} = x̂_per|Â_∞^{(ε)}` for **all** `ε ∈ ℤ_+`」，`:530` 收在「which contradicts the
maximality of `Â_i`」。`:518` 的 `Â_i^{(ε)} := {g - t·v⃗_{ℓ_{J+1}} ∈ Â_∞^{(ε)} : g ∈ Â_i, t ∈ ℤ_+}`
就是下面四条 binder 里的 `ShellMink.shellInter … w`；`:520` 的「is an `E(𝒮_φ)`-enveloped set」
就是那条共享的守卫前提；`:520` 的 `B_i - k_i v⃗_ℓ ⊂ Â_i^{(ε)} ⊂ H_{B_i}(ℓ) - k_i v⃗_ℓ`
就是 `shellSubStrip`。原文在 `:530` 相撞的两端是：

* 甲 = `Â_i^{(ε)} ⊋ Â_i`（严格性），**纯几何，与反证假设无关**——这就是 `escapeW`；
* 乙 = agreement ⟹ `Â_i^{(ε)} ⊆ Â_i`，由反证假设推出。

⚠ **原文一字未证甲**（`:518-530` 通篇没有），它是我们必须补的义务。
⚠ **`escapeW` 的证明里不许出现任何由反证假设导出的东西。** 内核见证：
`Nivat.LaneTowerHlevEscW.not_escapeW_of_agreement`（`tmp/wip/lane-tower-hlev-escapew.lean` §8）
证明守卫 + `shellSubStrip` + agreement ⟹ `¬ escapeW`，引擎是 `Colle35.maximalHat_of_max`
（`ChainMax.lean:117`）。

✅ **`escapeW` 已被正面证明，这条 binder 不再是义务（第 164 轮）。**
`Nivat.LaneTowerHlevEscPos.exists_I₀_escapeW`（**主仓** `EscapeW.lean`，按标识符找；
0 sorry，`[propext, Classical.choice, Quot.sound]`，集成者复跑 `check1.sh` EXIT=0 复核过。
⚠ 本段原先引的 `tmp/wip/lane-tower-hlev-escapew-pos.lean:304` 是 B 类腐烂——
那份 `tmp/wip/` 草稿的内容第 164 轮就搬进主仓了，2026-09-25 订正）：
结论逐字符是本结构 `escapeW` 字段（本文件，按字段名找——行号会无声腐烂，PROTOCOL §85）的
结论，外面套一个 `∃ I₀`；前提**全部**取自本表已有的 binder
（`AhatMono` / `hhp` / `hswept` / `ahat_nonempty` / `hsweep` / `hsweepW` / `rec_p` / `dot_nJ_p`，
外加 `F.dot_nJ_vJ`、`vJ_prim`、体内的 `rec_vJ'`、`bottom` 的前两合取）。
证法：二维 Cramer 把 `T • w` 拆成 `a • vJ + bb • vJ1`，`dot nJ vJ = 0` 逼出 `bb·d₁ = T·D > 0`；
取 `Â_∞` 中高度恰为 `cJ + T·D − 1` 的点，沿 `vJ` 平移吸收 `a` 的符号（高度不变），再走 `T` 步 `w`，
落点在 `reachSet` 内、高度 `cJ − 1`，由 `hhp` 白送「∉ `Â_i`」。**全程没用守卫、没用格凸性、
没用 `:516` 的反证假设**——这同时从构造上确认了上面那条 ⚠：`escapeW` 不需要守卫。

⚠ **2026-09-25 接线（lane-tower-hlev）**：`I₀` 在 `ChainAsm.Aparts.ChainDataGeomParts`
（`ChainPartsFeed.lean`）里是**字段**，与生产者交的 `∃ I₀` 同形，量词位置那条残差已关闭。
接好的那条是 `Nivat.LaneTowerHlevEscWire.chainDataGeomParts_of_chain_escapeW_free`
（`TowerHlevEscapeWire.lean`）：binder 表里既没有 `I₀` 也没有 `escapeW`，
`shellSubStrip` / `fillCover` 改收 `∃ I₀` 形，体内取三个阈值的 `max`。
**本结构（`ofPartsExhaustsInter`）的签名不动**，`I₀` 在这一层仍是 binder，由 `c.I₀` 喂。
（注意「不需要」≠「守卫惰性」。我第 162 轮在 `:71` 附近写过「守卫惰性」，已被
lane-tower-hlev 的 `envOf_guard_false_on_box` 推翻，见那里的更正。）
⚠ **不许把反证假设补进下面的 binder 表**——补进去等于让生产者活在反证语境里，甲端当场为假，
`RegionSteps.exists_chainData` 直接不可证。
`i₀` 这个 floor 的用途就在甲端：`:516` 的「for an appropriate `ε ∈ ℕ` fixed and all `i ∈ ℕ`
sufficiently large」保证 `Â_i` 已长到能够到 shell 里超出 `Â_∞` 的那些点。

`escapeW` / `shellSubStrip` / `fillCover` 三条共享逐字符相同的前缀，`shellEnv` 是这一组
**唯一**的存在量词、也是 `(ε, i₀)` 的唯一生产者（`fillCover` / `shellProper` 原来的 `∀ε`
已于第 159 轮被内核证伪删掉：`:530` 整句活在 `:516` 的「ε 固定、i 充分大」之下）。

**⚠ 同一道守卫，两种角色——别把两边的裁决互相援引（2026-09-24，第 162 轮）。**
三条前缀虽然逐字符相同，守卫 `∀ i, i₀ ≤ i → Env (shellInter …)` 起的作用却相反：

* `fillCover` 的守卫**承重**。它在 `i = i₀` 处直接卡住 `ε`：
  `Nivat.LaneLeafAGenInter.eps_lt_of_enveloped`（`tmp/wip/lane-leafa-gen-fillcover-inter.lean:535`）
  给出 `Enveloped ↑Shex (Yset i₀ ε) → ε < 2 * i₀ + 2`。同一实例上守卫版为真
  （`fillCover_repaired_instance`，同文件 `:588`，`Env = EnvOf ↑Shex`，`Shex` 见
  `ApexUnique.lean:469`），守卫非空真（`enveloped_Yset`，
  `tmp/wip/lane-leafa-gen-fillcover-inter.lean:615`，`(ε,i₀)=(1,0)`；
  ⚠ 2026-09-25 订正：原先写成紧跟在 `ApexUnique.lean:469` 后面的裸 `:620`，
  既指错了文件、行号也腐烂了两行，`PROTOCOL §57`）。
  第 154 轮之前那个无守卫的 `∀ i i₀ ε` 形状已被 `not_fillCover_binder`（同文件 `:360`）
  在 `(i,i₀,ε)=(2,0,5)` 上内核否掉——`5 > 2*0+2`，正是被这道守卫挡在门外。
  **该反例打的是 159 之前的形状，不是对现签名的活证伪。**
* `escapeW` 的守卫**同样承重**（2026-09-24 更正，第 163 轮）。我第 162 轮在这里写过
  「escapeW 的守卫惰性、只在乙端起作用」，那是错的，已被内核推翻：lane-tower-hlev 的
  `envOf_guard_false_on_box` / `escapeW_holds_on_box_with_envOf` 表明，取 `Env := EnvOf ↑S` 时
  这道守卫把 `E (shellInter … i)` 钉成对 `i` 常值——那是实打实的约束，不是摆设。
  所以「守卫什么也不供」这个说法作废，别再援引。

保留的只有一条弱得多的提醒：三条前缀逐字符相同，但它们各自的**消费者**不同，
证甲端的方向性论证不能直接搬去证乙端；要援引先核对方向。

**`w` 的扇形相邻性：有现货，但不进这张表（2026-09-24 裁决，第 162 轮）。**
本表对 `w` 的唯一约束是 `hsweepW : dot nJ w < 0`（`NOTATION.md` 的 `hsweepW` 条早记过这个缺口）。
**只拿 `hsweepW` 当前提是推不出 `shellEnv` 的**：`Nivat.LaneEnvShellEnvRefute.not_shellEnv`
（`tmp/wip/lane-env-shellenv-refute.lean`）在一个具体台架上取 `w = (-1,-1)`（满足 `hsweepW`）
内核否掉了 `shellEnv` 的结论，⟹ 「`hsweepW` ⟹ `shellEnv`」为假。缺的那条是扇形相邻性。

⚠ **别把 `shellEnv_fan`（同文件）读成「扇后继 ⟹ `shellEnv`」的生产者**（第 201 轮订正，
集成者；上一版这段的写法害得派过一轮不可执行的工）。它是**同一台架上换 `w = (-1,0)` 后
结论为真的单点见证，零前提、不带任何全称量词**，只说明反例不是普遍现象、方向是对的；
它**不是** ∀-形式的定理，不能把 `Arc J νJ1 = ∅` 当输入串进去。真要那一步得另证。
（两条都在 `tmp/`，按 §16 不得被主仓 import，此处只作记录，不是可援引的依据。）

它已经有 0-sorry 的生产者：`Nivat.LeafAShellNNext.exists_w_hsweepW`（`LeafAShellNNext.lean:75`）
的结论里带 `0 < det J νJ1 ∧ Arc (Sphi.finite_toSet) J νJ1 = ∅ ∧ w = -(dir νJ1)`，
`Arc J νJ1 = ∅` 就是「`J` 与 `νJ1` 之间没有别的边法向」。取值 `w = -(dir νJ1)` 对得上原文
`b3_colle2.txt:518` 的 `v⃗_{ℓ_{J+1}}`（`NOTATION.md` 的 `w` 条），`nJ = -J`（`NOTATION.md:175,208`）。

⛔ **但「`νJ1` 是 `J` 的扇邻居」没有原文锚点**（2026-09-24 裁决，集成者）：`:518` 亲读是
`Â_i^{(ε)}` 的定义，只给 `w` 的取值公式，**不主张相邻性**。`Arc J νJ1 = ∅` 是
`exists_w_hsweepW` 自己构造出来的，是我们补的一步，按硬规矩 5 记债，援引时不得挂到 `:518`。

**不往本表加这几条 binder**，因为 `shellEnv` / `shellSubStrip` / `fillCover` 都是**调用方供给**
的 binder，不是本定义内部消费的——调用方证 `shellEnv` 时，`exists_w_hsweepW` 解构出来的
相邻性本来就在作用域里。加进来只会多出一组没有消费者的 binder，那是纯债（硬规矩 5），
不是修复。⟹ 接法是在**调用方一侧**把这两项用掉。**第 181 轮已接**（集成者，
`WFanWiring.lean`）：`Nivat.WFanWiring.exists_w_fan_dichotomy` 用扇后继消掉
`LaneCdSubstrip.w_eq_vl_or_dot_nl_w_neg`（`ShellSubStrip.lean:136`）的 `hor` 假设，
`fan_w_shellSubStrip_or_finite` 把两支接到 `shellSubStrip_of_w_eq_vl_of_max` /
`shellInter_finite_of_level` 上，交出「`shellSubStrip` 当场成立 **或** `:518` 的壳有限」。
⚠ **那里不主张 `shellEnv`**——有限性 ≠ `Env`，本条 binder 的缺口仍在。

⛔ **订正 2026-09-24（集成者，第 207 轮；行号按 §85 已改成标识符名，原写 `:2561` 早腐烂到 `:2572`，
lane-tower-hlev 抓）**：这里原来写 `LaneCdM4.shellEnv_false_at_m_four`「仍然有效」，**读起来像它否掉
本 binder，那是错的**。它有效，但**有作用域**：同文件那段自述的 **Not encoded** 清单里列着
`Exhausts` / `shellSubStrip` / `escapeW` / `fillCover` / `bottom` / 整个 `Config`·`PeriodOn` 侧，
它的 `T` 是个**简化代用品**（`⋃ hatOf` 是半带，不是 `(ℓ,ℓ_J)`-region）。
**而且导致它的那条推断已被同文件 §21 明文撤回**：`Nivat.LaneCdFan`（docstring 首句
"This section retracts §19's docstring alarm"）证明 §19「`shellEnv` 需 `m ≤ 3`」是**漏算**——
`Â_∞` 是楔形，在**整个极锥**上有限支撑而非两个方向，`recovered_of_sweep_deleted_dot` 给出
「`w`-扫掠删掉的法向要么是 `J`（被 `-n_J` cut 收回）、要么落在极锥里（被 `reachSet Â_∞ v_{J-1}` 收回）」，
**对任意 `m ≥ 2` 都不剩**〔⛔ 这半句已收窄，见下一段〕，`fan_receipt_arcs` / `fan_receipt_count`
是 `m = 4` 八边形的 `decide` 收据。
⟹ **不要把 §20 当成本 binder 的反证**；§20 现在的正面读法是「region 结构是承重的，
`rec_vJ'` / `side` / `bottom` 不可从 bundle 里删」。

⛔ **收窄 2026-09-24（集成者，第 209 轮；§14 原文不删）**：上一段「对任意 `m ≥ 2` 都不剩」**只在
`Arc ℓ J = ∅` 的分支上成立**，不是无条件的。`recovered_of_sweep_deleted_dot` 的前提 `harc_lJ`
逐字是「`E ↑S` 里没有严格介于 `ℓ` 与 `J` 之间的边法向」，而主仓自己的 `J` 选取机制
`LeafAJSelect.exists_fan_pred` **把这明写成退化分支**：它对 `Arc ℓ J` 做 `eq_empty_or_nonempty`，
空的那支才给 `nprevJ = ℓ`，一般情形 `nprevJ` 严格落在 `Arc ℓ J` 里、交出的是 `Arc nprevJ J = ∅`
（该定理 docstring 逐字「or `ℓ` itself when `Arc ℓ J = ∅`（team-lead's stated degenerate case）」）。
§21 唯一的数值收据（八边形 `N8`）正好是这个退化实例，所以它测不到一般分支。
把 §21 的 `ℓ` 换成 `nprevJ` **不能救**：`harc_lJ` 兑现了，但结论退化成 `det nprevJ n ≤ 0`，
**盖不住** `Â_∞` 的极锥 `{det ℓ · ≤ 0} ∩ {det J · ≤ 0}`——差的恰好是介于 `ℓ` 与 `nprevJ` 之间那批法向。
⟹ §19 的 `m ≤ 3` 警报仍然是被撤回的（那条推断本身漏算，与 `harc_lJ` 无关），但「法向计数对任意 `m` 都关掉了」
**不是**已证事实。一般分支的数值实例在造（lane-hole3-nlmax）。
§21 自己标的 **Still owed** 是另一件事：那 `m` 条极锥法向确实是 `Â_∞` 的**边**、且面长不短于 `𝒮_φ`
（`b3_colle2.txt:500-504`），主树尚无。 -/
noncomputable def ChainDataGeom.ofPartsExhaustsInter
    (η xper : Config α) (vl p : ℤ × ℤ) (S : Finset (ℤ × ℤ)) (gen : ℤ × ℤ)
    (Env : Set (ℤ × ℤ) → Prop) (B A : ℕ → Set (ℤ × ℤ)) (u : ℕ → ℤ × ℤ) (kk : ℕ → ℕ)
    (envShift : ∀ (v : ℤ × ℤ) (T : Set (ℤ × ℤ)), Env T → Env {z | z + v ∈ T})
    (envB : ∀ i, Env (B i))
    (maxA : ∀ i, IsMaxEnvIn Env (canonA η xper vl B u i) (A i))
    (subBA : ∀ i, B i ⊆ A i) (subAB : ∀ i, A i ⊆ B (i + 1))
    (AhatMono : ∀ i j, i ≤ j → hatOf A kk vl i ⊆ hatOf A kk vl j)
    (vJ1 nJ : ℤ × ℤ) (cJ : ℤ)
    (hsweep : dot nJ vJ1 < 0)
    (hfin : ∀ i, (hatOf A kk vl i).Finite)
    (hhp : ∀ i, hatOf A kk vl i ⊆ halfPlaneGE nJ cJ)
    (hswept : SweptClosed (⋃ i, hatOf A kk vl i) vJ1 nJ cJ)
    (ahat_nonempty : (⋃ i, hatOf A kk vl i).Nonempty)
    (w : ℤ × ℤ) (hsweepW : dot nJ w < 0)
    -- **`I₀`（第 162 轮）**：原文 `b3_colle2.txt:520` 的第二个常数，`:524`
    -- 「if we consider `i ≥ max{i₀, I₀}`」。见 `ChainData.I₀`（`Lemma35.lean`）。
    (I₀ : ℕ)
    (escapeW : ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → Env (ShellMink.shellInter (hatOf A kk vl i)
        (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w)) →
      ∀ i, max i₀ I₀ ≤ i → ∃ g ∈ hatOf A kk vl i, ∃ t : ℕ,
      g + (t : ℤ) • w ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε ∧
      g + (t : ℤ) • w ∉ hatOf A kk vl i)
    (shellSubStrip : ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → Env (ShellMink.shellInter (hatOf A kk vl i)
        (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w)) →
      ∀ i, max i₀ I₀ ≤ i →
      ShellMink.shellInter (hatOf A kk vl i)
          (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w ⊆
        {z | z + (kk i : ℤ) • vl ∈ halfStrip (B i) vl})
    (shellEnv : ∃ ε i₀, 0 < ε ∧ ∀ i, i₀ ≤ i →
      Env (ShellMink.shellInter (hatOf A kk vl i)
        (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w))
    (fillCover : ∀ ε i₀ : ℕ, 0 < ε →
      (∀ i, i₀ ≤ i → Env (ShellMink.shellInter (hatOf A kk vl i)
        (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w)) →
      ∀ i, max i₀ I₀ ≤ i →
      ShellMink.shellInter (hatOf A kk vl i)
          (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w ⊆
        {z | Colle37.GenClosure S (hatOf A kk vl i ∪
          ShellMink.shellInter (hatOf A kk vl i₀)
            (MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε) w) z})
    (vJ : ℤ × ℤ) (F : FaceBlock S nJ vJ)
    (gen_eq : gen = F.a')
    (vJ_prim : Primitive vJ) (nJ_prim : Primitive nJ)
    (bottom : ∀ ε : ℕ, ∃ (z₀ : ℤ × ℤ) (L : ℤ),
      dot nJ z₀ = cJ - (ε : ℤ) - 1 ∧
      (∀ k : ℤ, L ≤ k → z₀ + k • vJ ∈ reachSet (⋃ i, hatOf A kk vl i) vJ1) ∧
      (∀ b ∈ S, ∀ k : ℤ, L ≤ k →
        z₀ + k • vJ + (b - F.a) ∈ reachSet (⋃ i, hatOf A kk vl i) vJ1) ∧
      (∀ z ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ (ε + 1),
        z ∈ MaxEnv.shell (⋃ i, hatOf A kk vl i) vJ1 nJ cJ ε ∨
          ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • vJ))
    (rec_p : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + p ∈ ⋃ i, hatOf A kk vl i)
    (dot_nJ_p : dot nJ p ≠ 0)
    (hEnv : Env = EnvOf (↑S : Set (ℤ × ℤ)))
    (nℓ : ℤ × ℤ) (cz : ℤ) (hprim : Primitive nℓ) (hperp : dot nℓ vl = 0)
    (hvl : vl ≠ 0) (hdet : det p vl = 0)
    -- **`hp_per`（第 212 轮，lane-leafa-shell；集成者批准）**：原文
    -- `scratch/b3_colle2.txt:496` —— 「Since $x_{per}\in X_{\eta}$ is a periodic
    -- configuration with period parallel to $\boldsymbol{\ell}$」。
    -- 逐量词对应：原文那个 period ↦ `p`；`x_per` ↦ `xper`；「is a periodic configuration
    -- with period」↦ `p ∈ Per xper`（`Per` 的 carrier 是 `{u | T u f = f}`，
    -- `Nivat/Defs/Config.lean:62`，展开即 `∀ z, xper (z + p) = xper z`）；
    -- 「parallel to `ℓ`」不在这条里，它就是同处已有的 `hdet : det p vl = 0`，不重复收。
    -- ⚠ 这条**不是**新债：唯一构造点（`tmp/wip/LeafAAssemble.lean` §`exists_chainData`）
    -- 签名里本来就有 `hp_mem : p ∈ Per xper` 且此前零使用，白送。加它的作用是**解除**
    -- 第 211 轮那个「binder 表推不出 `shellSubStrip`」的反证。
    -- **辖域订正（第 214 轮）**：否掉的不是 `Oct8Bench.lean` 的 `px = (-1,-1)` 这**一个**取值，
    -- 而是**整族 `p`**。两步，主仓有内核收据：
    --   1. `xperx = fun w => w.1 = 0` 的周期群整个落在竖轴上——`Per xperx ⊆ {h | h.1 = 0}`
    --      （`Nivat.LaneTowerOct8.mem_Per_xperx_fst_zero`，取 `z := (-h.1, 0)`）；
    --   2. 同处的 `hdet : det p vl = 0` 把 `p` 钉在 `vlx = (1,1)` 方向上。两者只交于 `p = 0`。
    -- 于是 `dot_nJ_p` 垮掉，`det p vJ ≠ 0` 也跟着垮掉：哨兵
    -- `Nivat.LaneTowerOct8.no_p_satisfies_hp_per_hdet_dot_nJ_p`（撞 `dot_nJ_p`，那是表的**输入**
    -- binder，划不掉）与 `no_p_satisfies_hp_per_and_hdet`（撞 `det p vJ ≠ 0`）。
    -- ⚠ **第 215 轮更新**：`hpvJ : det p vJ ≠ 0` 已不再是 binder（见体内 `let hpvJ`），它现在由
    -- `vJ_prim`＋`F.dot_nJ_vJ`＋`dot_nJ_p` 推出。这不削弱上面的论证，反而收紧了它：后一个哨兵
    -- 撞的那条现在是**推论**，而它的前提 `dot_nJ_p` 正是前一个哨兵撞的那条输入 binder，
    -- ⟹ 两个哨兵现在撞的是同一条划不掉的 binder，不必再担心「靠 `hpvJ` 可能被删」。
    -- ⟹ 要让那个台架重新落进本表辖域，**换 `p` 没有出路，只能换
    -- `xper`**（同结论：lane-tower-hbase 的 `px_shape_not_per`）。旧口径「`px` 不是周期」留了
    -- 「换个 `p` 也许能修」的口子，那个口子不存在。
    -- 尚无消费者：`shellSubStrip` 的证明还没用上它。故本行会自报一条
    -- `Variable name 'hp_per' is not explicitly referenced` 的 warning——那是**有意留着**的，
    -- 是「本条只封辖域、尚未供货」的自报家门；改成 `_hp_per` 等于把债藏进下划线。
    -- 它该消失的时点只有一个：`shellSubStrip` 的证明真的用上 `hp_per` 之日，届时 warning 自动
    -- 消失；在那之前不许以 lint 噪音为由清掉。
    (hp_per : p ∈ Per xper)
    (hexh : Exhausts A nℓ cz)
    (hnotDP : ¬ ∃ h h' : ℤ × ℤ, det h h' ≠ 0 ∧
      PeriodicOnWith xper {z | cz ≤ dot nℓ z} h ∧ PeriodicOnWith xper {z | cz ≤ dot nℓ z} h') :
    ChainDataGeom η xper vl p S gen :=
  let rec_vJ' : ∀ g ∈ ⋃ i, hatOf A kk vl i, g + vJ ∈ ⋃ i, hatOf A kk vl i :=
    rec_vJ_of_bottom (latticeConvex_iUnion_hatOf η xper vl S Env B A u kk hEnv maxA hfin AhatMono)
      hsweep (fun _ hg => Set.iUnion_subset hhp hg) hswept F.dot_nJ_vJ bottom
  -- `det p vJ ≠ 0` 曾是本表的 binder `hpvJ`（第 215 轮删，lane-env-refute）。它是**推得出来的**：
  -- `vJ_prim`（经 `Primitive.ne_zero`）＋ `F.dot_nJ_vJ`＋`dot_nJ_p` 三条本表现成的 binder 喂进
  -- `Nivat.ColleReg.det_ne_zero_of_dot`（`ChainGeom.lean`，标识符锚点，§85.3）即得。
  -- 同一条推导在 `ChainGeom.lean` 的 `region_periods_and_rays_of_geom` 证明体里本来就有
  -- （`have hdetpv := det_ne_zero_of_dot cg.vJ_ne cg.dot_nJ_vJ cg.dot_nJ_p`）。
  -- ⚠ 这是**减一条冗余 binder**，不是放宽结论：`ell_side_of_exhausts` 拿到的 `det p vJ ≠ 0`
  -- 与从前逐字相同，只是改由本表内部产出，不再向调用者索取。
  let hpvJ : det p vJ ≠ 0 :=
    Nivat.ColleReg.det_ne_zero_of_dot vJ_prim.ne_zero F.dot_nJ_vJ dot_nJ_p
  let side := ell_side_of_exhausts (xper := xper) (Ahat := hatOf A kk vl) hvl hdet hpvJ hprim
    hperp (fun i => hatOf_eq i) hexh rec_vJ' hnotDP
  ChainDataGeom.ofPartsInter η xper vl p S gen Env B A u kk envShift envB maxA subBA subAB
    AhatMono vJ1 nJ cJ hsweep hfin hhp hswept ahat_nonempty w hsweepW I₀ escapeW shellSubStrip
    shellEnv fillCover vJ F gen_eq vJ_prim nJ_prim bottom rec_p dot_nJ_p rec_vJ'
    side.choose_spec.choose
    side.choose_spec.choose_spec.2.2.2.1
    side.choose_spec.choose_spec.2.2.2.2.1
    side.choose_spec.choose_spec.2.2.2.2.2

end Nivat.Colle35

#print axioms Nivat.Colle35.ChainDataGeom.ofPartsExhaustsInter
