/-
Lane lane-cd-edgeunb (sub-lane of lane-chaindata-lead), 2026-09-22.  `tmp/wip/`, 0 sorry.

Task: strengthen `Nivat.LeafAEdgeUnbounded.exists_edge_unbounded`
(`Nivat/External/Colle/LeafAEdgeUnbounded.lean:165`) from a disjunction to a conjunction —
BOTH sides of `nℓ` carry an unbounded face, not just one.

We may not edit `LeafAEdgeUnbounded.lean`, and its telescoping core (`supp_pair_le`,
`mul_le_of_le_of_le`) is `private` to that file, hence unreachable from here.  So this file
re-derives the same two lemmas (verbatim copies) and reassembles the two halves of the
original `exists_edge_unbounded` proof into two independent one-sided lemmas
(`width_bound` for the width step common to both arcs, `false_of_width_bound` for the final
numeric contradiction, shared verbatim by both arcs), then discharges each conjunct by
`by_contra` separately.

## The extra hypothesis, and why it is needed

The original proof's Step 1 produces *one* intermediate normal `ν` with `det nℓ ν ≠ 0`; which
of the two open half-planes (`0 < det nℓ ν` or `0 < det ν nℓ`) it lands in is not under the
caller's control.  To prove the *left* conjunct alone (`by_contra` supplies only the
"`0 < det nℓ ·` side is bounded" hypothesis, not the other), we need a normal on that specific
side.  If Step 1's `ν` lands on the wrong side, `-ν` lands on the right one (since
`det nℓ (-ν) = - det nℓ ν`) — provided `-ν ∈ E ↑Sphi` too.  That is exactly the "`E` of an
enveloped set is closed under negation" fact.  There is **no** general lemma of that shape for
a bare `Enveloped U T` hypothesis in `Nivat/External/Colle/*`: every `negSymm`-flavoured lemma
found (`Colle35.Sphi_negSymm` `DecompData.lean:417`, `DecompData.neg_mem_E_Sphi_of_dot_eq_zero`
`FaceDistinct.lean:159`, `ONEDRational.mem_E_Sphi_and_neg_mem_E_Sphi_of_biONED`
`ONEDRational.lean:201`) is stated for a `Colle35.DecompData`/`DecompDataZ`, i.e. needs `Sphi`
to actually be the zonotope of a decomposition, not just an arbitrary finite set with
`Enveloped ↑Sphi (A i)` for each `i`.  Indeed a bare finite `Sphi` need not have `E` symmetric:
nothing stops `Sphi` itself from being an asymmetric lattice polygon.  So we add

`hSymm : ∀ μ ∈ E ↑Sphi, -μ ∈ E ↑Sphi`

as an explicit extra hypothesis.  At the real call site (where `Sphi` comes from a
`DecompData`), this is exactly `(Colle35.Sphi_negSymm d.toDecompData μ).mp`, so it costs the
caller nothing.
-/
import Nivat.External.Colle.LeafAEdgeUnbounded

set_option autoImplicit false

namespace Nivat.LaneCdEdgeUnb

open Nivat Nivat.LE2 Nivat.PolyChain Nivat.PolyChainSum Nivat.Colle35

/-! ## §0. Verbatim copies of the two private helpers from `LeafAEdgeUnbounded.lean`

`mul_le_of_le_of_le` and `supp_pair_le` are `private` there, hence not importable; reproduced
here unchanged (mod name) since editing that file is out of scope. -/

private theorem mul_le_of_le_of_le {f d Lz Mz : ℤ} (h0 : 0 ≤ f) (hL : f ≤ Lz)
    (hd : d ≤ Mz) (hM : 0 ≤ Mz) : f * d ≤ Lz * Mz := by
  have hL0 : 0 ≤ Lz := le_trans h0 hL
  rcases le_total 0 d with hd0 | hd0
  · calc f * d ≤ Lz * d := mul_le_mul_of_nonneg_right hL hd0
      _ ≤ Lz * Mz := mul_le_mul_of_nonneg_left hd hL0
  · have h1 : 0 ≤ f * (-d) := mul_nonneg h0 (by linarith)
    have h2 : 0 ≤ Lz * Mz := mul_nonneg hL0 hM
    nlinarith

private theorem supp_pair_le {T : Set (ℤ × ℤ)} (hfin : T.Finite)
    (hlc : IsLatticeConvexRegion T) {p ν : ℤ × ℤ} {EFix : Finset (ℤ × ℤ)} {K : ℤ}
    (hp : p ∈ E T) (hnp : -p ∈ E T) (hν : ν ∈ E T) (hdet : 0 < det ν p)
    (hK0 : 0 ≤ K) (hK : ∀ μ ∈ E T, 0 < det μ p → (faceLen T μ : ℤ) * det μ p ≤ K)
    (hsub : ∀ μ ∈ E T, μ ∈ EFix) :
    suppVal T p + suppVal T (-p) ≤ (2 * (EFix.card : ℤ) + 1) * K := by
  have hsum : ∀ F : Finset (ℤ × ℤ), (∀ μ ∈ F, μ ∈ E T) → (∀ μ ∈ F, 0 < det μ p) →
      ∑ μ ∈ F, (faceLen T μ : ℤ) * det μ p ≤ (EFix.card : ℤ) * K := by
    intro F hF hFd
    have h1 : ∑ μ ∈ F, (faceLen T μ : ℤ) * det μ p ≤ ∑ _μ ∈ F, K :=
      Finset.sum_le_sum fun μ hμ => hK μ (hF μ hμ) (hFd μ hμ)
    have h2 : F ⊆ EFix := fun μ hμ => hsub μ (hF μ hμ)
    have h3 : (F.card : ℤ) ≤ (EFix.card : ℤ) := by exact_mod_cast Finset.card_le_card h2
    have h4 : ∑ _μ ∈ F, K = (F.card : ℤ) * K := by rw [Finset.sum_const, nsmul_eq_mul]
    have h5 : (F.card : ℤ) * K ≤ (EFix.card : ℤ) * K := mul_le_mul_of_nonneg_right h3 hK0
    linarith
  have hflip : ∀ a b : ℤ × ℤ, det (-a) b = det b a := by
    intro a b; simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
  have hdetnp : 0 < det (-p) ν := by rw [hflip]; exact hdet
  have hvec := chain_ccw_final hfin hlc hnp hν hdetnp
  have hsc := chain_ccw_scalar_final hfin hlc hν hp hdet
  have hII : dot p (faceStart T ν) - dot p (faceStart T (-p))
      = ∑ μ ∈ (finite_E_of_finite hfin).toFinset.filter
          (fun μ => 0 < det (-p) μ ∧ 0 < det μ ν), (faceLen T μ : ℤ) * det μ p := by
    have h := congrArg (dot p) hvec
    rw [dot_sub, dot_add, dot_zsmul_right, dot_dir_right, dot_sum] at h
    have hz : det (-p) p = 0 := by
      simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
    rw [hz, mul_zero, zero_add] at h
    rw [h]
    exact Finset.sum_congr rfl fun μ _ => by rw [dot_zsmul_right, dot_dir_right]
  have hsn : suppVal T (-p) = - dot p (faceStart T (-p)) := by
    rw [suppVal_eq (faceStart_mem hfin hnp), dot_neg_left]
  have hb1 := hsum ((finite_E_of_finite hfin).toFinset.filter
      (fun μ => 0 < det (-p) μ ∧ 0 < det μ ν))
      (fun μ hμ => (finite_E_of_finite hfin).mem_toFinset.mp (Finset.mem_filter.mp hμ).1)
      (fun μ hμ => by
        have h := (Finset.mem_filter.mp hμ).2.1
        rwa [hflip] at h)
  have hb2 := hsum ((finite_E_of_finite hfin).toFinset.filter
      (fun μ => 0 < det ν μ ∧ 0 < det μ p))
      (fun μ hμ => (finite_E_of_finite hfin).mem_toFinset.mp (Finset.mem_filter.mp hμ).1)
      (fun μ hμ => (Finset.mem_filter.mp hμ).2.2)
  have hb3 : (faceLen T ν : ℤ) * det ν p ≤ K := hK ν hν hdet
  linarith

/-! ## §1. Step 1 (finding a non-parallel normal), independent of any boundedness hypothesis

Verbatim reproduction of Step 1 of `exists_edge_unbounded`; does not depend on `hcon1`/`hcon2`
at all, so it is shared unchanged by both conjuncts. -/

private theorem exists_normal_not_parallel
    {A B : ℕ → Set (ℤ × ℤ)} {Sphi : Finset (ℤ × ℤ)} {nℓ : ℤ × ℤ} {cz : ℤ}
    (hnℓ : nℓ ≠ 0)
    (hItemII : ItemII B nℓ cz) (hsubBA : ∀ i, B i ⊆ A i)
    (hfin : ∀ i, (A i).Finite)
    (henv : ∀ i, Enveloped (↑Sphi : Set (ℤ × ℤ)) (A i)) :
    ∃ ν ∈ E (↑Sphi : Set (ℤ × ℤ)), det nℓ ν ≠ 0 := by
  have hEfinS : (E (↑Sphi : Set (ℤ × ℤ))).Finite := finite_E_of_finite Sphi.finite_toSet
  have hEeq : ∀ i, E (A i) = E (↑Sphi : Set (ℤ × ℤ)) :=
    fun i => Enveloped.E_eq hEfinS (henv i)
  have hcoord : nℓ.1 ≠ 0 ∨ nℓ.2 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hnℓ (by simp [Prod.ext_iff, hc.1, hc.2])
  have hP0 : 0 < dot nℓ nℓ := by
    simp only [dot]
    rcases hcoord with h | h
    · nlinarith [mul_self_pos.mpr h, mul_self_nonneg nℓ.2]
    · nlinarith [mul_self_pos.mpr h, mul_self_nonneg nℓ.1]
  have hq1 : -(|nℓ.1| + |nℓ.2|) ≤ nℓ.1 := by
    have := neg_abs_le nℓ.1; have := abs_nonneg nℓ.2; omega
  have hq2 : nℓ.1 ≤ |nℓ.1| + |nℓ.2| := by
    have := le_abs_self nℓ.1; have := abs_nonneg nℓ.2; omega
  have hq3 : -(|nℓ.1| + |nℓ.2|) ≤ nℓ.2 := by
    have := neg_abs_le nℓ.2; have := abs_nonneg nℓ.1; omega
  have hq4 : nℓ.2 ≤ |nℓ.1| + |nℓ.2| := by
    have := le_abs_self nℓ.2; have := abs_nonneg nℓ.1; omega
  have hmemG : ∀ (z : ℤ × ℤ) (i : ℕ), -((i : ℤ) - 1) ≤ z.1 → z.1 ≤ (i : ℤ) - 1 →
      -((i : ℤ) - 1) ≤ z.2 → z.2 ≤ (i : ℤ) - 1 → cz ≤ dot nℓ z → z ∈ A i :=
    fun z i a1 a2 b1 b2 h3 =>
      hsubBA i (hItemII i z (abs_le.mpr ⟨a1, a2⟩) (abs_le.mpr ⟨b1, b2⟩) h3)
  have hdotscale : ∀ c : ℤ, dot nℓ ((c * nℓ.1, c * nℓ.2) : ℤ × ℤ) = c * dot nℓ nℓ := by
    intro c; simp only [dot]; ring
  have hmemScale : ∀ (c : ℤ) (i : ℕ), 0 ≤ c → cz ≤ c * dot nℓ nℓ →
      c * (|nℓ.1| + |nℓ.2|) ≤ (i : ℤ) - 1 → ((c * nℓ.1, c * nℓ.2) : ℤ × ℤ) ∈ A i := by
    intro c i hc hcz hbd
    refine hmemG _ i ?_ ?_ ?_ ?_ (by rw [hdotscale]; exact hcz)
    · have h := mul_le_mul_of_nonneg_left hq1 hc
      nlinarith
    · have h := mul_le_mul_of_nonneg_left hq2 hc
      linarith
    · have h := mul_le_mul_of_nonneg_left hq3 hc
      nlinarith
    · have h := mul_le_mul_of_nonneg_left hq4 hc
      linarith
  set c₀ : ℤ := max cz 0 with hc₀def
  have hc₀0 : 0 ≤ c₀ := le_max_right _ _
  have hc₀cz : cz ≤ c₀ := le_max_left _ _
  have hc₀dot : cz ≤ c₀ * dot nℓ nℓ := by nlinarith
  set Rb : ℤ := c₀ * (|nℓ.1| + |nℓ.2|) + (|nℓ.1| + |nℓ.2|) with hRbdef
  have hQ0 : 0 ≤ |nℓ.1| + |nℓ.2| := by
    have := abs_nonneg nℓ.1; have := abs_nonneg nℓ.2; omega
  have hcQ : 0 ≤ c₀ * (|nℓ.1| + |nℓ.2|) := mul_nonneg hc₀0 hQ0
  have hRb0 : 0 ≤ Rb := by rw [hRbdef]; omega
  set i₁ : ℕ := Rb.toNat + 1 with hi₁def
  have hi₁ : ((i₁ : ℕ) : ℤ) - 1 = Rb := by rw [hi₁def]; push_cast; omega
  have hm1 := mul_le_mul_of_nonneg_left hq1 hc₀0
  have hm2 := mul_le_mul_of_nonneg_left hq2 hc₀0
  have hm3 := mul_le_mul_of_nonneg_left hq3 hc₀0
  have hm4 := mul_le_mul_of_nonneg_left hq4 hc₀0
  have hA : ((c₀ * nℓ.1, c₀ * nℓ.2) : ℤ × ℤ) ∈ A i₁ := by
    refine hmemScale c₀ i₁ hc₀0 hc₀dot ?_
    rw [hi₁, hRbdef]; omega
  have hB : ((c₀ * nℓ.1 - nℓ.2, c₀ * nℓ.2 + nℓ.1) : ℤ × ℤ) ∈ A i₁ := by
    refine hmemG _ i₁ ?_ ?_ ?_ ?_ ?_
    · rw [hi₁, hRbdef]; nlinarith
    · rw [hi₁, hRbdef]; nlinarith
    · rw [hi₁, hRbdef]; nlinarith
    · rw [hi₁, hRbdef]; nlinarith
    · have h : dot nℓ ((c₀ * nℓ.1 - nℓ.2, c₀ * nℓ.2 + nℓ.1) : ℤ × ℤ) = c₀ * dot nℓ nℓ := by
        simp only [dot]; ring
      rw [h]; exact hc₀dot
  have hC : ((c₀ * nℓ.1 + nℓ.1, c₀ * nℓ.2 + nℓ.2) : ℤ × ℤ) ∈ A i₁ := by
    refine hmemG _ i₁ ?_ ?_ ?_ ?_ ?_
    · rw [hi₁, hRbdef]; nlinarith
    · rw [hi₁, hRbdef]; nlinarith
    · rw [hi₁, hRbdef]; nlinarith
    · rw [hi₁, hRbdef]; nlinarith
    · have h : dot nℓ ((c₀ * nℓ.1 + nℓ.1, c₀ * nℓ.2 + nℓ.2) : ℤ × ℤ)
          = c₀ * dot nℓ nℓ + dot nℓ nℓ := by
        simp only [dot]; ring
      rw [h]; linarith
  have hPos : PosArea (A i₁) := by
    refine ⟨_, hA, _, hB, _, hC, ?_⟩
    have h : det
        (((c₀ * nℓ.1 - nℓ.2, c₀ * nℓ.2 + nℓ.1) : ℤ × ℤ) - ((c₀ * nℓ.1, c₀ * nℓ.2) : ℤ × ℤ))
        (((c₀ * nℓ.1 + nℓ.1, c₀ * nℓ.2 + nℓ.2) : ℤ × ℤ) - ((c₀ * nℓ.1, c₀ * nℓ.2) : ℤ × ℤ))
        = - dot nℓ nℓ := by
      simp only [det, dot, Prod.fst_sub, Prod.snd_sub]; ring
    rw [h]; omega
  obtain ⟨ν, hνE, hνdot⟩ :=
    exists_mem_E_dot_ne_zero (hfin i₁) ⟨_, hA⟩ hPos (dir_ne_zero hnℓ)
  refine ⟨ν, by rw [← hEeq i₁]; exact hνE, ?_⟩
  rw [← dot_dir_gen nℓ ν]; exact hνdot

/-! ## §2. The width bound for one arc, `p` generic (`nℓ` or `-nℓ`)

This is exactly the `hlt`-branch body of the original `exists_edge_unbounded` (lines
320-333 there), with `nℓ` replaced by a generic `p` so that a single call proves the bound
for whichever side actually has a boundedness hypothesis; the caller instantiates `p := nℓ`
directly for the right conjunct, or `p := -nℓ` (then rewrites `-(-nℓ) = nℓ`) for the left. -/

private theorem width_bound
    {A : ℕ → Set (ℤ × ℤ)} {Sphi : Finset (ℤ × ℤ)} {p ν : ℤ × ℤ}
    (hfin : ∀ i, (A i).Finite)
    (henv : ∀ i, Enveloped (↑Sphi : Set (ℤ × ℤ)) (A i))
    (hpE : p ∈ E (↑Sphi : Set (ℤ × ℤ))) (hnpE : -p ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hνE : ν ∈ E (↑Sphi : Set (ℤ × ℤ))) (hdet : 0 < det ν p)
    (hcon : ∀ μ ∈ E (↑Sphi : Set (ℤ × ℤ)), 0 < det μ p → ∃ L : ℕ, ∀ i, faceLen (A i) μ ≤ L) :
    ∃ D : ℤ, ∀ i, suppVal (A i) p + suppVal (A i) (-p) ≤ D := by
  have hEfinS : (E (↑Sphi : Set (ℤ × ℤ))).Finite := finite_E_of_finite Sphi.finite_toSet
  have hEeq : ∀ i, E (A i) = E (↑Sphi : Set (ℤ × ℤ)) :=
    fun i => Enveloped.E_eq hEfinS (henv i)
  have hlcA : ∀ i, IsLatticeConvexRegion (A i) := fun i => (henv i).1.1
  choose! Lf hLf using hcon
  set EF : Finset (ℤ × ℤ) := hEfinS.toFinset with hEFdef
  have hmemEF : ∀ μ, μ ∈ EF ↔ μ ∈ E (↑Sphi : Set (ℤ × ℤ)) := fun μ => hEfinS.mem_toFinset
  obtain ⟨Lb, hLbd⟩ :
      ∃ Lb : ℕ, ∀ μ ∈ E (↑Sphi : Set (ℤ × ℤ)), 0 < det μ p → ∀ i, faceLen (A i) μ ≤ Lb :=
    ⟨EF.sup Lf, fun μ hμ hd i =>
      le_trans (hLf μ hμ hd i) (Finset.le_sup (f := Lf) ((hmemEF μ).mpr hμ))⟩
  obtain ⟨Mb, hMbd⟩ :
      ∃ Mb : ℕ, ∀ μ ∈ E (↑Sphi : Set (ℤ × ℤ)), (det μ p).natAbs ≤ Mb :=
    ⟨EF.sup (fun x => (det x p).natAbs),
      fun μ hμ => Finset.le_sup (f := fun x => (det x p).natAbs) ((hmemEF μ).mpr hμ)⟩
  refine ⟨(2 * (EF.card : ℤ) + 1) * ((Lb : ℤ) * (Mb : ℤ)), fun i => ?_⟩
  have hK0 : (0 : ℤ) ≤ (Lb : ℤ) * (Mb : ℤ) :=
    mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hνT : ν ∈ E (A i) := by rw [hEeq i]; exact hνE
  have hpT : p ∈ E (A i) := by rw [hEeq i]; exact hpE
  have hnpT : -p ∈ E (A i) := by rw [hEeq i]; exact hnpE
  have hsubT : ∀ μ ∈ E (A i), μ ∈ EF := by
    intro μ hμ; rw [hEeq i] at hμ; exact (hmemEF μ).mpr hμ
  have hK : ∀ μ ∈ E (A i), 0 < det μ p →
      (faceLen (A i) μ : ℤ) * det μ p ≤ (Lb : ℤ) * (Mb : ℤ) := by
    intro μ hμ hdμ
    have hμS : μ ∈ E (↑Sphi : Set (ℤ × ℤ)) := by rw [← hEeq i]; exact hμ
    have hd : det μ p ≤ (Mb : ℤ) := by have := hMbd μ hμS; omega
    have hnn : (0 : ℤ) ≤ (faceLen (A i) μ : ℤ) := Int.natCast_nonneg _
    have hle : (faceLen (A i) μ : ℤ) ≤ (Lb : ℤ) := by exact_mod_cast hLbd μ hμS hdμ i
    exact mul_le_of_le_of_le hnn hle hd (Int.natCast_nonneg _)
  exact supp_pair_le (hfin i) (hlcA i) hpT hnpT hνT hdet hK0 hK hsubT

/-! ## §3. Step 3 (the numeric contradiction), independent of which arc supplied `D`

Verbatim reproduction of Step 3 of `exists_edge_unbounded`, packaged so both conjuncts share
it once each side has produced its own width bound `D`. -/

private theorem false_of_width_bound
    {A B : ℕ → Set (ℤ × ℤ)} {nℓ : ℤ × ℤ} {cz D : ℤ}
    (hnℓ : nℓ ≠ 0)
    (hItemII : ItemII B nℓ cz) (hsubBA : ∀ i, B i ⊆ A i)
    (hfin : ∀ i, (A i).Finite)
    (hwidth : ∀ i, suppVal (A i) nℓ + suppVal (A i) (-nℓ) ≤ D) : False := by
  have hcoord : nℓ.1 ≠ 0 ∨ nℓ.2 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hnℓ (by simp [Prod.ext_iff, hc.1, hc.2])
  have hP0 : 0 < dot nℓ nℓ := by
    simp only [dot]
    rcases hcoord with h | h
    · nlinarith [mul_self_pos.mpr h, mul_self_nonneg nℓ.2]
    · nlinarith [mul_self_pos.mpr h, mul_self_nonneg nℓ.1]
  have hP1 : 1 ≤ dot nℓ nℓ := by omega
  have hq1 : -(|nℓ.1| + |nℓ.2|) ≤ nℓ.1 := by
    have := neg_abs_le nℓ.1; have := abs_nonneg nℓ.2; omega
  have hq2 : nℓ.1 ≤ |nℓ.1| + |nℓ.2| := by
    have := le_abs_self nℓ.1; have := abs_nonneg nℓ.2; omega
  have hq3 : -(|nℓ.1| + |nℓ.2|) ≤ nℓ.2 := by
    have := neg_abs_le nℓ.2; have := abs_nonneg nℓ.1; omega
  have hq4 : nℓ.2 ≤ |nℓ.1| + |nℓ.2| := by
    have := le_abs_self nℓ.2; have := abs_nonneg nℓ.1; omega
  have hQ0 : 0 ≤ |nℓ.1| + |nℓ.2| := by
    have := abs_nonneg nℓ.1; have := abs_nonneg nℓ.2; omega
  have hmemG : ∀ (z : ℤ × ℤ) (i : ℕ), -((i : ℤ) - 1) ≤ z.1 → z.1 ≤ (i : ℤ) - 1 →
      -((i : ℤ) - 1) ≤ z.2 → z.2 ≤ (i : ℤ) - 1 → cz ≤ dot nℓ z → z ∈ A i :=
    fun z i a1 a2 b1 b2 h3 =>
      hsubBA i (hItemII i z (abs_le.mpr ⟨a1, a2⟩) (abs_le.mpr ⟨b1, b2⟩) h3)
  have hdotscale : ∀ c : ℤ, dot nℓ ((c * nℓ.1, c * nℓ.2) : ℤ × ℤ) = c * dot nℓ nℓ := by
    intro c; simp only [dot]; ring
  have hmemScale : ∀ (c : ℤ) (i : ℕ), 0 ≤ c → cz ≤ c * dot nℓ nℓ →
      c * (|nℓ.1| + |nℓ.2|) ≤ (i : ℤ) - 1 → ((c * nℓ.1, c * nℓ.2) : ℤ × ℤ) ∈ A i := by
    intro c i hc hcz hbd
    refine hmemG _ i ?_ ?_ ?_ ?_ (by rw [hdotscale]; exact hcz)
    · have h := mul_le_mul_of_nonneg_left hq1 hc
      nlinarith
    · have h := mul_le_mul_of_nonneg_left hq2 hc
      linarith
    · have h := mul_le_mul_of_nonneg_left hq3 hc
      nlinarith
    · have h := mul_le_mul_of_nonneg_left hq4 hc
      linarith
  obtain ⟨c₀, hc₀0, hc₀cz⟩ : ∃ c : ℤ, 0 ≤ c ∧ cz ≤ c :=
    ⟨max cz 0, le_max_right _ _, le_max_left _ _⟩
  have hc₀dot : cz ≤ c₀ * dot nℓ nℓ := by nlinarith
  obtain ⟨t, ht0, htcz, htbig⟩ :
      ∃ t : ℤ, 0 ≤ t ∧ cz ≤ t ∧ D + c₀ * dot nℓ nℓ + 1 ≤ t :=
    ⟨max (max (D + c₀ * dot nℓ nℓ + 1) cz) 0, le_max_right _ _,
      le_trans (le_max_right _ _) (le_max_left _ _),
      le_trans (le_max_left _ _) (le_max_left _ _)⟩
  have htdot : cz ≤ t * dot nℓ nℓ := by nlinarith
  have hcQ : 0 ≤ c₀ * (|nℓ.1| + |nℓ.2|) := mul_nonneg hc₀0 hQ0
  have htQ : 0 ≤ t * (|nℓ.1| + |nℓ.2|) := mul_nonneg ht0 hQ0
  obtain ⟨i₂, hi₂⟩ :
      ∃ i₂ : ℕ, ((i₂ : ℕ) : ℤ) - 1 = c₀ * (|nℓ.1| + |nℓ.2|) + t * (|nℓ.1| + |nℓ.2|) :=
    ⟨(c₀ * (|nℓ.1| + |nℓ.2|) + t * (|nℓ.1| + |nℓ.2|)).toNat + 1, by push_cast; omega⟩
  have hz0 : ((c₀ * nℓ.1, c₀ * nℓ.2) : ℤ × ℤ) ∈ A i₂ := by
    refine hmemScale c₀ i₂ hc₀0 hc₀dot ?_
    rw [hi₂]; omega
  have hz1 : ((t * nℓ.1, t * nℓ.2) : ℤ × ℤ) ∈ A i₂ := by
    refine hmemScale t i₂ ht0 htdot ?_
    rw [hi₂]; omega
  have hne : (A i₂).Nonempty := ⟨_, hz0⟩
  have hup : dot nℓ ((t * nℓ.1, t * nℓ.2) : ℤ × ℤ) ≤ suppVal (A i₂) nℓ :=
    le_suppVal (hfin i₂) hne hz1
  have hlow : dot (-nℓ) ((c₀ * nℓ.1, c₀ * nℓ.2) : ℤ × ℤ) ≤ suppVal (A i₂) (-nℓ) :=
    le_suppVal (hfin i₂) hne hz0
  rw [dot_neg_left, hdotscale] at hlow
  rw [hdotscale] at hup
  have hw := hwidth i₂
  nlinarith [hup, hlow, hw, htbig, hP1, ht0]

/-! ## §4. The `∧` theorem -/

/-- **Task, strengthened.**  Same hypotheses as
`Nivat.LeafAEdgeUnbounded.exists_edge_unbounded`, plus `hSymm` (see the module docstring for
why it is necessary and where it is free): BOTH sides of `nℓ` carry a fixed edge normal with
unbounded face length across the chain, not just one. -/
theorem exists_edge_unbounded_both
    {A B : ℕ → Set (ℤ × ℤ)} {Sphi : Finset (ℤ × ℤ)} {nℓ : ℤ × ℤ} {cz : ℤ}
    (hnℓ : nℓ ≠ 0)
    (hItemII : ItemII B nℓ cz) (hsubBA : ∀ i, B i ⊆ A i)
    (hfin : ∀ i, (A i).Finite)
    (henv : ∀ i, Enveloped (↑Sphi : Set (ℤ × ℤ)) (A i))
    (hnℓE : nℓ ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hnegnℓE : (-nℓ) ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hSymm : ∀ μ ∈ E (↑Sphi : Set (ℤ × ℤ)), -μ ∈ E (↑Sphi : Set (ℤ × ℤ))) :
    (∃ ν ∈ E (↑Sphi : Set (ℤ × ℤ)), 0 < det nℓ ν ∧ ¬ ∃ L : ℕ, ∀ i, faceLen (A i) ν ≤ L) ∧
    (∃ ν ∈ E (↑Sphi : Set (ℤ × ℤ)), 0 < det ν nℓ ∧ ¬ ∃ L : ℕ, ∀ i, faceLen (A i) ν ≤ L) := by
  classical
  obtain ⟨ν0, hν0S, hν0det⟩ := exists_normal_not_parallel hnℓ hItemII hsubBA hfin henv
  have hmir : ∀ μ : ℤ × ℤ, det μ (-nℓ) = det nℓ μ := by
    intro μ; simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
  constructor
  · -- Left conjunct: `0 < det nℓ ν`.
    by_contra hc
    have hcon1 : ∀ ν ∈ E (↑Sphi : Set (ℤ × ℤ)), 0 < det nℓ ν →
        ∃ L : ℕ, ∀ i, faceLen (A i) ν ≤ L := by
      intro ν hν hd
      by_contra h
      exact hc ⟨ν, hν, hd, h⟩
    -- Get a witness on the `0 < det nℓ ·` side, flipping `ν0` via `hSymm` if needed.
    obtain ⟨ν, hνS, hνdet⟩ : ∃ ν ∈ E (↑Sphi : Set (ℤ × ℤ)), 0 < det nℓ ν := by
      rcases lt_or_gt_of_ne hν0det with hlt | hgt
      · exact ⟨-ν0, hSymm ν0 hν0S, by
          have : det nℓ (-ν0) = - det nℓ ν0 := by
            simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
          omega⟩
      · exact ⟨ν0, hν0S, hgt⟩
    have hdetMirror : 0 < det ν (-nℓ) := by rw [hmir]; exact hνdet
    have hconMirror : ∀ μ ∈ E (↑Sphi : Set (ℤ × ℤ)), 0 < det μ (-nℓ) →
        ∃ L : ℕ, ∀ i, faceLen (A i) μ ≤ L := by
      intro μ hμ hdμ
      exact hcon1 μ hμ (by rw [← hmir]; exact hdμ)
    obtain ⟨D, hwidth⟩ := width_bound hfin henv hnegnℓE
      (by rw [neg_neg]; exact hnℓE) hνS hdetMirror hconMirror
    have hwidth' : ∀ i, suppVal (A i) nℓ + suppVal (A i) (-nℓ) ≤ D := by
      intro i
      have h := hwidth i
      rw [neg_neg] at h
      linarith
    exact false_of_width_bound hnℓ hItemII hsubBA hfin hwidth'
  · -- Right conjunct: `0 < det ν nℓ`.
    by_contra hc
    have hcon2 : ∀ ν ∈ E (↑Sphi : Set (ℤ × ℤ)), 0 < det ν nℓ →
        ∃ L : ℕ, ∀ i, faceLen (A i) ν ≤ L := by
      intro ν hν hd
      by_contra h
      exact hc ⟨ν, hν, hd, h⟩
    obtain ⟨ν, hνS, hνdet⟩ : ∃ ν ∈ E (↑Sphi : Set (ℤ × ℤ)), 0 < det ν nℓ := by
      rcases lt_or_gt_of_ne hν0det with hlt | hgt
      · exact ⟨ν0, hν0S, by rw [det_skew ν0 nℓ]; omega⟩
      · exact ⟨-ν0, hSymm ν0 hν0S, by
          have h1 : det (-ν0) nℓ = - det ν0 nℓ := by
            simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
          have h2 : det ν0 nℓ = - det nℓ ν0 := det_skew ν0 nℓ
          omega⟩
    obtain ⟨D, hwidth⟩ := width_bound hfin henv hnℓE hnegnℓE hνS hνdet hcon2
    exact false_of_width_bound hnℓ hItemII hsubBA hfin hwidth

#print axioms Nivat.LaneCdEdgeUnb.exists_edge_unbounded_both

end Nivat.LaneCdEdgeUnb
