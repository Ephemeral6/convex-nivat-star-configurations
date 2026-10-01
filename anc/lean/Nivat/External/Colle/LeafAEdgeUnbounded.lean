/-
Lane leafa, 2026-09-22.  `tmp/wip/`, 0 incomplete proofs.

Team-lead task (i): "for a chain of `Sphi`-enveloped finite regions `A i` whose item-(ii)
boxes grow, some normal `ν ∈ E ↑Sphi` has `faceLen (A i) ν` unbounded in `i`."

The conclusion carries a **determinant-sign tag** saying which side of `nℓ` the witness is
on, as a disjunction of the two `hunb` hypotheses of `tmp/wip/LeafAJSelect.lean` (lane-recp):
`exists_J_stable` consumes the `0 < det nℓ ν` disjunct, `exists_J_stable_cw` the mirror
`0 < det ν nℓ` one.  The witness is never parallel to `nℓ` (step 1 below), so no third case.

Signature is the stub of `tmp/wip/LeafAJSelect.lean` (lane-recp, `exists_edge_unbounded`,
`§2`) plus three hypotheses, all of which hold at the real call site:

* `hnℓ : nℓ ≠ 0` — without it the statement is FALSE (see "Found gap" below);
* `hnℓE : nℓ ∈ E ↑Sphi` and `hnegnℓE : -nℓ ∈ E ↑Sphi` — the two support normals of the
  half plane `ℋ(ℓ^(−))`, which are the two ends of the boundary walk used below.

## Found gap in the original stub signature

Without `nℓ ≠ 0`, `ItemII B nℓ cz` can be satisfied vacuously by `B := fun _ => ∅` (take
`nℓ = 0`, `cz = 1`: the guard `cz ≤ dot nℓ z` is `1 ≤ 0`, always false, so `ItemII` holds
for *any* `B`, including all-empty). Then `A := fun _ => ∅`, `Sphi := ∅` satisfies every other
hypothesis (`hsubBA`, `hfin`, `henv` — `Enveloped ∅ ∅` holds by `enveloped_refl`) while the
conclusion `∃ ν ∈ E ↑Sphi, … ∨ ∃ ν ∈ E ↑Sphi, …` is vacuously false (`E ∅ = ∅`, so both
disjuncts are). So the stub as literally written
is **false** without `nℓ ≠ 0`; it is a hypothesis below.
-/
import Nivat.External.Colle.PolyChainSum
import Nivat.External.Colle.ItemII

set_option autoImplicit false

namespace Nivat.LeafAEdgeUnbounded

open Nivat Nivat.LE2 Nivat.PolyChain Nivat.PolyChainSum Nivat.Colle35

/-! ## §0. Two elementary lemmas -/

/-- `f * d ≤ Lz * Mz` whenever `0 ≤ f ≤ Lz`, `d ≤ Mz` and `0 ≤ Mz`.  Note there is no lower
bound on `d`: if `d < 0` the left side is `≤ 0 ≤ Lz * Mz`. -/
private theorem mul_le_of_le_of_le {f d Lz Mz : ℤ} (h0 : 0 ≤ f) (hL : f ≤ Lz)
    (hd : d ≤ Mz) (hM : 0 ≤ Mz) : f * d ≤ Lz * Mz := by
  have hL0 : 0 ≤ Lz := le_trans h0 hL
  rcases le_total 0 d with hd0 | hd0
  · calc f * d ≤ Lz * d := mul_le_mul_of_nonneg_right hL hd0
      _ ≤ Lz * Mz := mul_le_mul_of_nonneg_left hd hL0
  · have h1 : 0 ≤ f * (-d) := mul_nonneg h0 (by linarith)
    have h2 : 0 ≤ Lz * Mz := mul_nonneg hL0 hM
    nlinarith

/-- **The two-sided support bound.**

Walk the boundary of a finite lattice-convex `T` counter-clockwise from the face with outer
normal `-p` to the face with outer normal `p`, through one intermediate edge normal `ν`
(`0 < det ν p`; note `det (-p) ν = det ν p`, so that single inequality already says `ν` lies
strictly between `-p` and `p` on the counter-clockwise arc).  Pairing the walk with `p`
telescopes to

`suppVal T p + suppVal T (-p) = Σ_{Arc(-p,ν)} faceLen·det + faceLen ν · det ν p
                                                     + Σ_{Arc(ν,p)} faceLen·det`,

because the `faceLen T (-p) • dir (-p)` step contributes `faceLen T (-p) * det (-p) p = 0`.
Every summand is `≤ K`, and there are at most `2 * |EFix| + 1` of them.

`hK` only has to bound the summands that actually occur, i.e. those with `0 < det μ p`:
on the arc `Arc(-p,ν)` the membership condition `0 < det (-p) μ` *is* `0 < det μ p`, on the
arc `Arc(ν,p)` it is the second conjunct verbatim, and the isolated `ν` term is `hdet`.  No
bound is needed on normals parallel to `p` (in particular on `±p`), which is what lets the
caller feed in a boundedness hypothesis restricted to one open half plane. -/
private theorem supp_pair_le {T : Set (ℤ × ℤ)} (hfin : T.Finite)
    (hlc : IsLatticeConvexRegion T) {p ν : ℤ × ℤ} {EFix : Finset (ℤ × ℤ)} {K : ℤ}
    (hp : p ∈ E T) (hnp : -p ∈ E T) (hν : ν ∈ E T) (hdet : 0 < det ν p)
    (hK0 : 0 ≤ K) (hK : ∀ μ ∈ E T, 0 < det μ p → (faceLen T μ : ℤ) * det μ p ≤ K)
    (hsub : ∀ μ ∈ E T, μ ∈ EFix) :
    suppVal T p + suppVal T (-p) ≤ (2 * (EFix.card : ℤ) + 1) * K := by
  -- A uniform bound for every chain sum occurring below.
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
  -- `det (-a) b = det b a`: this single identity is what makes the guard `0 < det μ p`
  -- available for free at every place `hK` is used below.
  have hflip : ∀ a b : ℤ × ℤ, det (-a) b = det b a := by
    intro a b; simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
  have hdetnp : 0 < det (-p) ν := by rw [hflip]; exact hdet
  have hvec := chain_ccw_final hfin hlc hnp hν hdetnp
  have hsc := chain_ccw_scalar_final hfin hlc hν hp hdet
  -- Pair the vector walk `-p ⇝ ν` with `p`.
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
  -- `suppVal T (-p)` is minus the `p`-height of the starting vertex.
  have hsn : suppVal T (-p) = - dot p (faceStart T (-p)) := by
    rw [suppVal_eq (faceStart_mem hfin hnp), dot_neg_left]
  -- On the first arc the membership condition `0 < det (-p) μ` *is* `0 < det μ p`.
  have hb1 := hsum ((finite_E_of_finite hfin).toFinset.filter
      (fun μ => 0 < det (-p) μ ∧ 0 < det μ ν))
      (fun μ hμ => (finite_E_of_finite hfin).mem_toFinset.mp (Finset.mem_filter.mp hμ).1)
      (fun μ hμ => by
        have h := (Finset.mem_filter.mp hμ).2.1
        rwa [hflip] at h)
  -- On the second arc `0 < det μ p` is literally the second conjunct.
  have hb2 := hsum ((finite_E_of_finite hfin).toFinset.filter
      (fun μ => 0 < det ν μ ∧ 0 < det μ p))
      (fun μ hμ => (finite_E_of_finite hfin).mem_toFinset.mp (Finset.mem_filter.mp hμ).1)
      (fun μ hμ => (Finset.mem_filter.mp hμ).2.2)
  have hb3 : (faceLen T ν : ℤ) * det ν p ≤ K := hK ν hν hdet
  linarith

/-! ## §1. Task (i) -/

/-- **Task (i).**  If `B` satisfies item (ii)'s box growth (`ItemII B nℓ cz`, radius-`(i-1)`
boxes of `ℋ(ℓ^(−))` land in `B i`) with `nℓ ≠ 0`, `B i ⊆ A i`, each `A i` finite, and each
`A i` is `Sphi`-enveloped (so `E (A i) = E Sphi`, a single *fixed* finite normal fan for every
`i`), then some fixed edge normal `ν ∈ E Sphi` has unbounded face length across the chain.

Moreover the witness comes tagged with the sign of `det nℓ ν`, so the caller knows which of
the two arcs bounded by `±nℓ` it lies on.

**Proof (contrapositive).**  Suppose both disjuncts fail.  That gives boundedness only for
the `ν ∈ E ↑Sphi` with `0 < det nℓ ν` and for those with `0 < det ν nℓ` — nothing at all for
the ones parallel to `nℓ`, and in particular nothing for `±nℓ`.  Take `Lb` the (finite)
maximum of the two bounding functions over the fixed finite fan `E ↑Sphi`, so that
`faceLen (A i) ν ≤ Lb` for every `i` and every `ν` on *either* open side, and let `Mb` bound
`|det μ nℓ|` over the same fan.  Both are `i`-independent because `E (A i) = E ↑Sphi`
(`Enveloped.E_eq`).

1. *A third edge normal.*  `ItemII` puts the three points `z₀`, `z₀ + dir nℓ`, `z₀ + nℓ`
   (where `z₀ = c₀ • nℓ` sits on the half plane) into `A i₁` for one explicit `i₁`, and
   `det (dir nℓ) nℓ = -⟪nℓ,nℓ⟫ ≠ 0`, so `PosArea (A i₁)`.  Then
   `exists_mem_E_dot_ne_zero` applied to `dir nℓ ≠ 0` produces `ν ∈ E (A i₁) = E ↑Sphi`
   with `det nℓ ν ≠ 0`, i.e. `ν` is **not** parallel to `nℓ`.  This is the one place
   positive area is needed: without it `E ↑Sphi` could be just `{nℓ, -nℓ}` and there would
   be no boundary walk from `-nℓ` to `nℓ` at all.

2. *Uniform width.*  `ν` lies strictly between `-nℓ` and `nℓ` on one of the two arcs;
   `supp_pair_le` (applied with `p := nℓ` or, on the other arc, with `p := -nℓ`, the two
   cases being mirror images) gives, for **every** `i`,
   `suppVal (A i) nℓ + suppVal (A i) (-nℓ) ≤ D` with `D := (2|E ↑Sphi| + 1) · Lb · Mb`
   independent of `i`.  This is the "bounded edge lengths ⟹ bounded width" step; note it
   bounds the *width* of `A i` in the direction `nℓ`, never its position — which is why the
   fixed anchor `z₀` is still needed in step 3.  `supp_pair_le`'s `hK` hypothesis is guarded
   by `0 < det μ p`, which on the `p := nℓ` arc reads `0 < det μ nℓ` and on the `p := -nℓ`
   arc reads `0 < det nℓ μ` — precisely the two restricted boundedness hypotheses above, so
   the half-plane-restricted bounds are enough and nothing is assumed about `±nℓ`.

3. *Contradiction.*  `ItemII` also puts `z₀` and a far point `z₁ = t • nℓ` with
   `⟪nℓ,z₁⟫ > D + ⟪nℓ,z₀⟫` into one common `A i₂`.  Then `le_suppVal` gives
   `⟪nℓ,z₁⟫ ≤ suppVal (A i₂) nℓ` and `-⟪nℓ,z₀⟫ = ⟪-nℓ,z₀⟫ ≤ suppVal (A i₂) (-nℓ)`, so
   `⟪nℓ,z₁⟫ - ⟪nℓ,z₀⟫ ≤ D`, contradicting the choice of `t`. -/
theorem exists_edge_unbounded
    {A B : ℕ → Set (ℤ × ℤ)} {Sphi : Finset (ℤ × ℤ)} {nℓ : ℤ × ℤ} {cz : ℤ}
    (hnℓ : nℓ ≠ 0)
    (hItemII : ItemII B nℓ cz) (hsubBA : ∀ i, B i ⊆ A i)
    (hfin : ∀ i, (A i).Finite)
    (henv : ∀ i, Enveloped (↑Sphi : Set (ℤ × ℤ)) (A i))
    (hnℓE : nℓ ∈ E (↑Sphi : Set (ℤ × ℤ)))
    (hnegnℓE : (-nℓ) ∈ E (↑Sphi : Set (ℤ × ℤ))) :
    (∃ ν ∈ E (↑Sphi : Set (ℤ × ℤ)), 0 < det nℓ ν ∧ ¬ ∃ L : ℕ, ∀ i, faceLen (A i) ν ≤ L) ∨
    (∃ ν ∈ E (↑Sphi : Set (ℤ × ℤ)), 0 < det ν nℓ ∧ ¬ ∃ L : ℕ, ∀ i, faceLen (A i) ν ≤ L) := by
  classical
  by_contra hcon
  -- Negating the disjunction gives two *sign-restricted* boundedness hypotheses.  Neither
  -- says anything about normals parallel to `nℓ` (in particular about `±nℓ` themselves) —
  -- and none is needed, because `supp_pair_le` now only calls `hK` on normals `μ` with
  -- `0 < det μ p`, i.e. strictly inside the relevant open half plane.
  have hcon1 : ∀ ν ∈ E (↑Sphi : Set (ℤ × ℤ)), 0 < det nℓ ν →
      ∃ L : ℕ, ∀ i, faceLen (A i) ν ≤ L := by
    intro ν hν hd
    by_contra h
    exact hcon (Or.inl ⟨ν, hν, hd, h⟩)
  have hcon2 : ∀ ν ∈ E (↑Sphi : Set (ℤ × ℤ)), 0 < det ν nℓ →
      ∃ L : ℕ, ∀ i, faceLen (A i) ν ≤ L := by
    intro ν hν hd
    by_contra h
    exact hcon (Or.inr ⟨ν, hν, hd, h⟩)
  -- ### The fixed normal fan
  have hEfinS : (E (↑Sphi : Set (ℤ × ℤ))).Finite := finite_E_of_finite Sphi.finite_toSet
  have hEeq : ∀ i, E (A i) = E (↑Sphi : Set (ℤ × ℤ)) :=
    fun i => Enveloped.E_eq hEfinS (henv i)
  have hlcA : ∀ i, IsLatticeConvexRegion (A i) := fun i => (henv i).1.1
  -- ### `⟪nℓ,nℓ⟫ ≥ 1` and the coordinate bound `Q = |nℓ.1| + |nℓ.2|`
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
  -- ### `ItemII` membership, in the two-sided form
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
  -- ### Step 1: a third edge normal, not parallel to `nℓ`
  obtain ⟨ν, hνS, hνdet⟩ : ∃ ν ∈ E (↑Sphi : Set (ℤ × ℤ)), det nℓ ν ≠ 0 := by
    set c₀ : ℤ := max cz 0 with hc₀def
    have hc₀0 : 0 ≤ c₀ := le_max_right _ _
    have hc₀cz : cz ≤ c₀ := le_max_left _ _
    have hc₀dot : cz ≤ c₀ * dot nℓ nℓ := by nlinarith
    set Rb : ℤ := c₀ * (|nℓ.1| + |nℓ.2|) + (|nℓ.1| + |nℓ.2|) with hRbdef
    have hcQ : 0 ≤ c₀ * (|nℓ.1| + |nℓ.2|) := mul_nonneg hc₀0 hQ0
    have hRb0 : 0 ≤ Rb := by rw [hRbdef]; omega
    set i₁ : ℕ := Rb.toNat + 1 with hi₁def
    have hi₁ : ((i₁ : ℕ) : ℤ) - 1 = Rb := by rw [hi₁def]; push_cast; omega
    have habs1 := le_abs_self nℓ.1
    have habs2 := le_abs_self nℓ.2
    have hnabs1 := neg_abs_le nℓ.1
    have hnabs2 := neg_abs_le nℓ.2
    have hA0 := abs_nonneg nℓ.1
    have hA1 := abs_nonneg nℓ.2
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
  -- ### Step 2: the uniform constants `Lb`, `Mb` and the width bound `D`
  choose! Lf1 hLf1 using hcon1
  choose! Lf2 hLf2 using hcon2
  set EF : Finset (ℤ × ℤ) := hEfinS.toFinset with hEFdef
  have hmemEF : ∀ μ, μ ∈ EF ↔ μ ∈ E (↑Sphi : Set (ℤ × ℤ)) := fun μ => hEfinS.mem_toFinset
  -- One `Lb` serving both signs; still no bound at all on normals parallel to `nℓ`.
  obtain ⟨Lb, hLbd1, hLbd2⟩ :
      ∃ Lb : ℕ,
        (∀ μ ∈ E (↑Sphi : Set (ℤ × ℤ)), 0 < det nℓ μ → ∀ i, faceLen (A i) μ ≤ Lb) ∧
        (∀ μ ∈ E (↑Sphi : Set (ℤ × ℤ)), 0 < det μ nℓ → ∀ i, faceLen (A i) μ ≤ Lb) := by
    refine ⟨EF.sup (fun x => max (Lf1 x) (Lf2 x)), ?_, ?_⟩
    · exact fun μ hμ hd i => le_trans (le_trans (hLf1 μ hμ hd i) (le_max_left _ _))
        (Finset.le_sup (f := fun x => max (Lf1 x) (Lf2 x)) ((hmemEF μ).mpr hμ))
    · exact fun μ hμ hd i => le_trans (le_trans (hLf2 μ hμ hd i) (le_max_right _ _))
        (Finset.le_sup (f := fun x => max (Lf1 x) (Lf2 x)) ((hmemEF μ).mpr hμ))
  obtain ⟨Mb, hMbd⟩ :
      ∃ Mb : ℕ, ∀ μ ∈ E (↑Sphi : Set (ℤ × ℤ)), (det μ nℓ).natAbs ≤ Mb :=
    ⟨EF.sup (fun x => (det x nℓ).natAbs),
      fun μ hμ => Finset.le_sup (f := fun x => (det x nℓ).natAbs) ((hmemEF μ).mpr hμ)⟩
  obtain ⟨D, hwidth⟩ :
      ∃ D : ℤ, ∀ i, suppVal (A i) nℓ + suppVal (A i) (-nℓ) ≤ D := by
    refine ⟨(2 * (EF.card : ℤ) + 1) * ((Lb : ℤ) * (Mb : ℤ)), fun i => ?_⟩
    have hK0 : (0 : ℤ) ≤ (Lb : ℤ) * (Mb : ℤ) :=
      mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    have hνT : ν ∈ E (A i) := by rw [hEeq i]; exact hνS
    have hnℓT : nℓ ∈ E (A i) := by rw [hEeq i]; exact hnℓE
    have hnnT : -nℓ ∈ E (A i) := by rw [hEeq i]; exact hnegnℓE
    have hsubT : ∀ μ ∈ E (A i), μ ∈ EF := by
      intro μ hμ; rw [hEeq i] at hμ; exact (hmemEF μ).mpr hμ
    rcases lt_trichotomy (det nℓ ν) 0 with hlt | heq | hgt
    · -- `ν` sits strictly between `-nℓ` and `nℓ` on the counter-clockwise arc; here `p := nℓ`
      -- and the guard `0 < det μ nℓ` is exactly the hypothesis `hLbd2` is restricted to.
      have hdet : 0 < det ν nℓ := by rw [det_skew ν nℓ]; omega
      have hK : ∀ μ ∈ E (A i), 0 < det μ nℓ →
          (faceLen (A i) μ : ℤ) * det μ nℓ ≤ (Lb : ℤ) * (Mb : ℤ) := by
        intro μ hμ hdμ
        have hμS : μ ∈ E (↑Sphi : Set (ℤ × ℤ)) := by rw [← hEeq i]; exact hμ
        have hd : det μ nℓ ≤ (Mb : ℤ) := by have := hMbd μ hμS; omega
        have hnn : (0 : ℤ) ≤ (faceLen (A i) μ : ℤ) := Int.natCast_nonneg _
        have hle : (faceLen (A i) μ : ℤ) ≤ (Lb : ℤ) := by
          exact_mod_cast hLbd2 μ hμS hdμ i
        exact mul_le_of_le_of_le hnn hle hd (Int.natCast_nonneg _)
      exact supp_pair_le (hfin i) (hlcA i) hnℓT hnnT hνT hdet hK0 hK hsubT
    · exact absurd heq hνdet
    · -- the mirror arc: the same walk with `p := -nℓ`; now the guard `0 < det μ (-nℓ)` is
      -- `0 < det nℓ μ`, exactly the hypothesis `hLbd1` is restricted to.
      have hmir : ∀ μ : ℤ × ℤ, det μ (-nℓ) = det nℓ μ := by
        intro μ; simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
      have hdet : 0 < det ν (-nℓ) := by rw [hmir]; exact hgt
      have hK : ∀ μ ∈ E (A i), 0 < det μ (-nℓ) →
          (faceLen (A i) μ : ℤ) * det μ (-nℓ) ≤ (Lb : ℤ) * (Mb : ℤ) := by
        intro μ hμ hdμ
        have hμS : μ ∈ E (↑Sphi : Set (ℤ × ℤ)) := by rw [← hEeq i]; exact hμ
        have hneg : det μ (-nℓ) = - det μ nℓ := by
          simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
        have hd : det μ (-nℓ) ≤ (Mb : ℤ) := by
          have := hMbd μ hμS; rw [hneg]; omega
        have hnn : (0 : ℤ) ≤ (faceLen (A i) μ : ℤ) := Int.natCast_nonneg _
        have hle : (faceLen (A i) μ : ℤ) ≤ (Lb : ℤ) := by
          have hdμ' : 0 < det nℓ μ := by rw [← hmir]; exact hdμ
          exact_mod_cast hLbd1 μ hμS hdμ' i
        exact mul_le_of_le_of_le hnn hle hd (Int.natCast_nonneg _)
      have h := supp_pair_le (hfin i) (hlcA i) hnnT (by rw [neg_neg]; exact hnℓT) hνT hdet
        hK0 hK hsubT
      rw [neg_neg] at h
      linarith
  -- ### Step 3: the contradiction
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

#print axioms Nivat.LeafAEdgeUnbounded.exists_edge_unbounded

end Nivat.LeafAEdgeUnbounded
