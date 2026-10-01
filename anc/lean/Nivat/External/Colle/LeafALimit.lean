import Nivat.Defs.Orbit
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

set_option autoImplicit false

namespace Nivat

/-!
`b3_colle2.txt:474-530` 的 item (ii) 论证核心是：给一列配置 `ϑ_i`，取一个「累积点」`ϑ_∞`，
使得它在任意有限窗口上、对无穷多个下标 `n` 与 `ϑ_n` 一致。`Defs/Orbit.lean:151` 的
`subseqLimits_nonempty` 已经用超滤子证过这件事的一个特例——`ϑ_n := T^{n•d} G`（单个配置沿
固定方向平移）。leaf A 用到的序列 `ϑ_i := T^{u_i} η`（`:480`）下标 `u_i` 不是线性的
（既有 `k_i v_ℓ` 又有横向的 `100i` 那种分量），所以不能直接套 `subseqLimits`；这里把同一个
超滤子论证从「单个配置的平移序列」推广到「任意配置序列」，证明与
`subseqLimits_nonempty` 逐行同构。 -/

/-- **任意（有限字母表上的）配置序列都有一个「处处窗口累积点」。**  推广自
`Nivat.subseqLimits_nonempty`（`Defs/Orbit.lean:151`）：那里的 `θ n := G (· + n • d)` 是
本引理的特例。证明技术相同——把 `atTop` 上的超滤子沿 `n ↦ θ n w` 推前，每个 `w` 对应的
超滤子在有限集 `α` 上必是主超滤子，读出极限值；再用超滤子对任意有限窗口、任意下界 `M`
都给出满足条件的下标 `n ≥ M`。 -/
theorem exists_limit_config {α : Type*} [Finite α] (θ : ℕ → Config α) :
    ∃ θinf : Config α, ∀ (W : Finset (ℤ × ℤ)) (M : ℕ),
      ∃ n : ℕ, M ≤ n ∧ ∀ w ∈ W, θinf w = θ n w := by
  classical
  set 𝔲 : Ultrafilter ℕ := Ultrafilter.of Filter.atTop with h𝔲
  have key : ∀ w : ℤ × ℤ, ∃ a : α, {n : ℕ | θ n w = a} ∈ 𝔲 := by
    intro w
    obtain ⟨a, ha⟩ := Ultrafilter.eq_pure_of_finite (Ultrafilter.map (fun n : ℕ => θ n w) 𝔲)
    refine ⟨a, ?_⟩
    have hmem : ({a} : Set α) ∈ Ultrafilter.map (fun n : ℕ => θ n w) 𝔲 := by
      rw [ha]; exact Ultrafilter.mem_pure.mpr rfl
    rwa [Ultrafilter.mem_map] at hmem
  choose y hy using key
  refine ⟨y, fun W M => ?_⟩
  have h1 : {n : ℕ | M ≤ n} ∈ 𝔲 := Ultrafilter.of_le Filter.atTop (Filter.mem_atTop M)
  have h2 : (⋂ w ∈ W, {n : ℕ | θ n w = y w}) ∈ 𝔲 :=
    (Filter.biInter_finset_mem W).mpr fun w _ => hy w
  obtain ⟨n, hn⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem h1 h2)
  refine ⟨n, hn.1, fun w hw => ?_⟩
  have hn2 := hn.2
  simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hn2
  exact (hn2 w hw).symm

/-- **The limit configuration lies in `η`'s orbit closure**, when every term of the sequence
does (e.g. `θ i := T^{u i} η`, via `T_mem_orbitClosure`).  This is exactly Collé's `ϑ_∞ ∈ X_η`
at `:498-506`: closure of the orbit closure (`orbitClosure_closed`) applied to the window
agreement furnished by `exists_limit_config`. -/
theorem exists_limit_mem_orbitClosure {α : Type*} [Finite α] {η : Config α} (θ : ℕ → Config α)
    (hθ : ∀ n, θ n ∈ orbitClosure η) :
    ∃ θinf ∈ orbitClosure η, ∀ (W : Finset (ℤ × ℤ)) (M : ℕ),
      ∃ n : ℕ, M ≤ n ∧ ∀ w ∈ W, θinf w = θ n w := by
  obtain ⟨θinf, hlim⟩ := exists_limit_config θ
  refine ⟨θinf, orbitClosure_closed ?_, hlim⟩
  intro W
  obtain ⟨n, -, hn⟩ := hlim W 0
  exact ⟨θ n, hθ n, hn⟩

#print axioms exists_limit_config
#print axioms exists_limit_mem_orbitClosure


/-- **Diagonal extraction along a growing sequence of finite windows.**  Iterates
`exists_limit_mem_orbitClosure` once per window, each time demanding the matching index be
past the previous one, so the resulting index sequence `n` is strictly increasing.  This is the
standard "diagonal argument" packaging that `b3_colle2.txt:496-506` invokes informally
("passing to a subsequence … `ϑ_i`") once `Â_i` (or any other growing family of finite windows)
is supplied by the caller. -/
theorem exists_limit_agreeing_along_growing_windows
    {α : Type*} [Finite α] {η : Config α} (θ : ℕ → Config α)
    (hθ : ∀ n, θ n ∈ orbitClosure η) (W : ℕ → Finset (ℤ × ℤ)) :
    ∃ θinf ∈ orbitClosure η, ∃ n : ℕ → ℕ, StrictMono n ∧
      ∀ i, ∀ w ∈ W i, θinf w = θ (n i) w := by
  classical
  obtain ⟨θinf, hmem, hlim⟩ := exists_limit_mem_orbitClosure θ hθ
  choose f hfM hfw using hlim
  let n : ℕ → ℕ := fun i => Nat.rec (f (W 0) 0) (fun j nj => f (W (j + 1)) (nj + 1)) i
  have hn0 : n 0 = f (W 0) 0 := rfl
  have hnsucc : ∀ j, n (j + 1) = f (W (j + 1)) (n j + 1) := fun j => rfl
  have hmono : ∀ j, n j < n (j + 1) := by
    intro j
    rw [hnsucc]
    have := hfM (W (j + 1)) (n j + 1)
    omega
  refine ⟨θinf, hmem, n, strictMono_nat_of_lt_succ hmono, fun i => ?_⟩
  cases i with
  | zero => rw [hn0]; exact hfw (W 0) 0
  | succ j => rw [hnsucc]; exact hfw (W (j + 1)) (n j + 1)

#print axioms exists_limit_agreeing_along_growing_windows

end Nivat
