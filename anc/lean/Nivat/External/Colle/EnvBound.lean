import Nivat.External.Colle.MaximalEnveloped

/-!
Probe (agent `envbound`, 2026-09-17): the geometric core of the "uniform bound" needed by
`RegionSteps.exists_chainData` to produce Colle's item (iv) maximal enveloped set.

⚠ Docstring corrected 2026-09-18: this said "`exists_chainData`'s **Zorn** step".  There is no
Zorn step, here or in Colle — `grep -c Zorn scratch/b3_colle2.txt` is 0, and the terminator
below is `Nivat.MaxEnv.exists_maximal_of_subset_finite` (`MaximalEnveloped.lean:227`), which
takes a *finite ambient set* and never forms a chain union.  That is the whole point of this
file: supplying the finite ambient set is the entire content of item (iv), and once it is
supplied no maximality principle beyond `Set.Finite.exists_maximal` is needed.  Anyone picking
up leaf A should not go looking for a chain-closure argument to translate.

Claim: if every member `T` of the family
  `{T | EnvOf U T ∧ B ⊆ T ∧ T ⊆ halfStrip B vl ∧ (agreement)}`
must avoid ONE fixed point `z₀ = b₀ + t₀•vl` of the half-strip (which Case 2 supplies, since
the family's members agree with `xper` on `T`), then the family is uniformly bounded.

No dynamics here: only the H-representation `mem_of_dot_le_suppVal` and `E T = E U`.
-/

set_option autoImplicit false

namespace Nivat.ProbeUB

open Nivat Nivat.LE2 Nivat.MaxEnv

theorem dot_smul_right (k : ℤ × ℤ) (g : ℤ) (v : ℤ × ℤ) : dot k (g • v) = g * dot k v := by
  rw [dot_comm, dot_smul, dot_comm]

/-- Excluding one point `z₀ = b₀ + t₀•vl` (with `b₀ ∈ T`) from an `E(U)`-enveloped `T`
produces an edge normal `k ∈ E U` with `⟪k, vl⟫ > 0` and `⟪k, ·⟫ < ⟪k, z₀⟫` on `T`. -/
theorem exists_normal_of_not_mem {U T : Set (ℤ × ℤ)} (hU : (E U).Finite)
    {n m : ℤ × ℤ} (hdet : det n m ≠ 0) (hn : n ∈ E U) (hn' : -n ∈ E U) (hm : m ∈ E U)
    (hm' : -m ∈ E U) (hT : EnvOf U T) {b₀ z₀ vl : ℤ × ℤ} {t₀ : ℕ} (hb₀ : b₀ ∈ T)
    (hz₀ : z₀ = b₀ + (t₀ : ℤ) • vl) (hz₀T : z₀ ∉ T) :
    ∃ k ∈ E U, 0 < dot k vl ∧ ∀ z ∈ T, dot k z < dot k z₀ := by
  have hfin : T.Finite := finite_of_envOf hU hdet hn hn' hm hm' hT
  have hne : T.Nonempty := ⟨b₀, hb₀⟩
  have hE : E T = E U := Enveloped.E_eq hU hT
  have h1 : n ≠ -n := by
    intro h
    have hn0 : n = 0 := by
      rw [Prod.ext_iff] at h ⊢
      simp only [Prod.fst_neg, Prod.snd_neg, Prod.fst_zero, Prod.snd_zero] at h ⊢
      omega
    apply hdet
    rw [hn0]; simp [det]
  have h2 : n ≠ m := by
    intro h; apply hdet; rw [h]; simp only [det]; ring
  have h3 : -n ≠ m := by
    intro h; apply hdet; rw [← h]; simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
  have harea : PosArea T := posArea_of_envOf hn hn' hm h1 h2 h3 hU hT
  by_contra hcon
  push Not at hcon
  apply hz₀T
  refine mem_of_dot_le_suppVal hfin hne harea hT.1.1 fun k hk => ?_
  rw [hE] at hk
  by_cases hkv : 0 < dot k vl
  · obtain ⟨z, hz, hzk⟩ := hcon k hk hkv
    exact hzk.trans (le_suppVal hfin hne hz)
  · push Not at hkv
    have hle : dot k z₀ ≤ dot k b₀ := by
      rw [hz₀, dot_add, dot_smul_right]
      nlinarith [Int.natCast_nonneg t₀]
    exact hle.trans (le_suppVal hfin hne hb₀)

/-- **Uniform bound.**  Fix `B` finite, `b₀ ∈ B`, `z₀ = b₀ + t₀•vl`.  There is `K` such that
every `E(U)`-enveloped `T ⊇ B` avoiding `z₀` satisfies: whenever `b + t•vl ∈ T` with
`b ∈ B`, `t ≤ K`.  `K` depends only on `U`, `B`, `z₀` — not on `T`. -/
theorem uniform_bound {U B : Set (ℤ × ℤ)} (hU : (E U).Finite)
    {n m : ℤ × ℤ} (hdet : det n m ≠ 0) (hn : n ∈ E U) (hn' : -n ∈ E U) (hm : m ∈ E U)
    (hm' : -m ∈ E U) (hB : B.Finite) {b₀ z₀ vl : ℤ × ℤ} {t₀ : ℕ} (hb₀ : b₀ ∈ B)
    (hz₀ : z₀ = b₀ + (t₀ : ℤ) • vl) :
    ∃ K : ℤ, ∀ T, EnvOf U T → B ⊆ T → z₀ ∉ T →
      ∀ b ∈ B, ∀ t : ℕ, b + (t : ℤ) • vl ∈ T → (t : ℤ) ≤ K := by
  have hfinI : ((fun p : (ℤ × ℤ) × (ℤ × ℤ) => dot p.1 z₀ - dot p.1 p.2) '' (E U ×ˢ B)).Finite :=
    (hU.prod hB).image _
  obtain ⟨K, hK⟩ := hfinI.bddAbove
  refine ⟨K, fun T hT hBT hz₀T b hb t ht => ?_⟩
  obtain ⟨k, hk, hkv, hlt⟩ :=
    exists_normal_of_not_mem hU hdet hn hn' hm hm' hT (hBT hb₀) hz₀ hz₀T
  have h1 := hlt _ ht
  rw [dot_add, dot_smul_right] at h1
  have h2 : dot k z₀ - dot k b ≤ K := hK ⟨(k, b), ⟨hk, hb⟩, rfl⟩
  nlinarith [Int.natCast_nonneg t]

/-- The finite window `W(B, vl, K) := {b + t•vl : b ∈ B, t ≤ K}`. -/
def window (B : Set (ℤ × ℤ)) (vl : ℤ × ℤ) (K : ℤ) : Set (ℤ × ℤ) :=
  {z | ∃ b ∈ B, ∃ t : ℕ, (t : ℤ) ≤ K ∧ z = b + (t : ℤ) • vl}

theorem window_finite {B : Set (ℤ × ℤ)} (hB : B.Finite) (vl : ℤ × ℤ) (K : ℤ) :
    (window B vl K).Finite := by
  have hsub : window B vl K ⊆
      (fun p : (ℤ × ℤ) × ℕ => p.1 + (p.2 : ℤ) • vl) '' (B ×ˢ Set.Iic K.toNat) := by
    rintro z ⟨b, hb, t, htK, rfl⟩
    refine ⟨(b, t), ⟨hb, ?_⟩, rfl⟩
    show t ≤ K.toNat
    exact_mod_cast htK.trans (Int.self_le_toNat K)
  exact ((hB.prod (Set.finite_Iic _)).image _).subset hsub

/-- **The family is contained in a finite window.**  This is exactly the `W.Finite` premise
of `Nivat.MaxEnv.exists_maximal_chainFamily`, so Colle's item (iv) maximal element exists. -/
theorem family_subset_window {U B : Set (ℤ × ℤ)} (hU : (E U).Finite)
    {n m : ℤ × ℤ} (hdet : det n m ≠ 0) (hn : n ∈ E U) (hn' : -n ∈ E U) (hm : m ∈ E U)
    (hm' : -m ∈ E U) (hB : B.Finite) {b₀ z₀ vl : ℤ × ℤ} {t₀ : ℕ} (hb₀ : b₀ ∈ B)
    (hz₀ : z₀ = b₀ + (t₀ : ℤ) • vl) :
    ∃ W : Set (ℤ × ℤ), W.Finite ∧
      ∀ T, EnvOf U T → B ⊆ T → T ⊆ halfStrip B vl → z₀ ∉ T → T ⊆ W := by
  obtain ⟨K, hK⟩ := uniform_bound hU hdet hn hn' hm hm' hB hb₀ hz₀
  refine ⟨window B vl K, window_finite hB vl K, fun T hT hBT hTH hz₀T z hz => ?_⟩
  obtain ⟨b, hb, t, rfl⟩ := hTH hz
  exact ⟨b, hb, t, hK T hT hBT hz₀T b hb t hz, rfl⟩

/-- **Colle's item (iv), with Case 2's disagreement point as input.**  Given `B` enveloped
(finite), `b₀ ∈ B`, the point `z₀ = b₀ + t₀•vl ∈ H_B(ℓ)` where `P` fails, and any `T₀` in
the agreement family, there is a maximal member of the family above `T₀`. -/
theorem exists_maximal_agreeFamily {U B : Set (ℤ × ℤ)} (hU : (E U).Finite)
    {n m : ℤ × ℤ} (hdet : det n m ≠ 0) (hn : n ∈ E U) (hn' : -n ∈ E U) (hm : m ∈ E U)
    (hm' : -m ∈ E U) (hB : B.Finite) {b₀ z₀ vl : ℤ × ℤ} {t₀ : ℕ} (hb₀ : b₀ ∈ B)
    (hz₀ : z₀ = b₀ + (t₀ : ℤ) • vl) {P : ℤ × ℤ → Prop} (hz₀P : ¬ P z₀)
    {T₀ : Set (ℤ × ℤ)} (h0 : T₀ ∈ chainFamily U B (halfStrip B vl) P) :
    ∃ M ∈ chainFamily U B (halfStrip B vl) P, T₀ ⊆ M ∧
      ∀ T ∈ chainFamily U B (halfStrip B vl) P, M ⊆ T → T = M := by
  obtain ⟨W, hWfin, hW⟩ := family_subset_window hU hdet hn hn' hm hm' hB hb₀ hz₀
  -- every member of the agreement family lies in `W`, so restrict and use the finite version
  have hsub : ∀ T ∈ chainFamily U B (halfStrip B vl) P, T ⊆ W := by
    rintro T ⟨hT, hBT, hTH, hP⟩
    exact hW T hT hBT hTH (fun hz => hz₀P (hP z₀ hz))
  exact exists_maximal_of_subset_finite hWfin _ hsub h0

end Nivat.ProbeUB

