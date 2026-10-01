/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges
import Nivat.External.Colle.PolyChain

/-!
# Boundary chain sums for lattice-convex polygons (Part (D) of `blueprint/LEAF-HSUPP.md`)

Colle, *On periodic decompositions …*, `b3_colle2.txt:402` (Definition 3.2), `:792-794`
(Claim 4.6's window).

`§2` proves the chain-sum theorem, part (D) of `blueprint/LEAF-HSUPP.md`, §2(D), abstractly
from three hypotheses (`hadjV`, `hseg`, `htrans`); `§4` instantiates them against
`lane-hsupp`'s landed `Nivat.External.Colle.PolyChain` (parts (A) `adjacent_shared_vertex`,
(B) `face_eq_segment`, (C) `det_pos_trans`), producing the final hypothesis-free theorems
`chain_ccw_final` / `chain_ccw_scalar_final` / `chain_cw_final` / `chain_cw_scalar_final`:

* `chain_ccw_final` : counter-clockwise boundary-walk identity
  `faceStart T n - faceStart T ν₀ = L(ν₀) • dir ν₀ + ∑_{Arc n} L(ν) • dir ν`
  for `ν₀, n ∈ E T` with `0 < det ν₀ n`, by strong induction on `|Arc n|`.
* `chain_ccw_scalar_final` : the scalar corollary (pairing both sides with `n`).
* `chain_cw_final`, `chain_cw_scalar_final` : the symmetric clockwise statements, which turn
  out to be literal relabellings of `chain_ccw` (swap `ν₀` and `n`).
-/

namespace Nivat.PolyChainSum

open Nivat.LE2

variable {T : Set (ℤ × ℤ)}
variable (faceStart : Set (ℤ × ℤ) → ℤ × ℤ → ℤ × ℤ) (faceLen : Set (ℤ × ℤ) → ℤ × ℤ → ℕ)

/-! ## §0. Small identities about `dir` that do not need `hadjV`/`hseg`/`htrans` -/

theorem dir_ne_zero {e : ℤ × ℤ} (he : e ≠ 0) : dir e ≠ 0 := by
  intro h
  apply he
  have h1 : -e.2 = 0 := by simpa [dir] using congrArg Prod.fst h
  have h2 : e.1 = 0 := by simpa [dir] using congrArg Prod.snd h
  have h3 : e.2 = 0 := by omega
  exact Prod.ext h2 h3

/-- `⟪x, dir n⟫ = det n x`, the general (both-argument) form of the identity
`blueprint/LEAF-HSUPP.md`, §0 records for `x := n` as `dot_dir`. -/
theorem dot_dir_gen (n x : ℤ × ℤ) : dot x (dir n) = det n x := by
  simp only [dot, dir, det]; ring

theorem dot_dir_left (n x : ℤ × ℤ) : dot (dir n) x = det n x := by
  rw [dot_comm]; exact dot_dir_gen n x

theorem dot_neg_dir (n x : ℤ × ℤ) : dot (-dir n) x = det x n := by
  rw [dot_neg_left, dot_dir_left, det_skew, neg_neg]

/-! ## §1. The maximal-element corollary of (C)

For a finite non-empty set of vectors all lying in one open half-plane `{det e · > 0}`,
there is an element `ν'` from which no other element is `det`-reachable (`0 < det ν' μ`
fails for every `μ` in the set). This is proved directly from the `rkey` angular-order
machinery already in `LatticeEdges.lean` (`rkey_le_iff`, `Finset.exists_max_image`); it
needs no input from `htrans`. -/

theorem exists_max_det {S : Finset (ℤ × ℤ)} {e : ℤ × ℤ} (he : e ≠ 0)
    (hSpos : ∀ ν ∈ S, 0 < det e ν) (hSne : S.Nonempty) :
    ∃ ν' ∈ S, ∀ μ ∈ S, ¬ (0 < det ν' μ) := by
  classical
  have hdirne : dir e ≠ 0 := dir_ne_zero he
  set c : ℝ × ℝ := toReal (-(dir e)) with hcdef
  have hconv : ∀ x : ℤ × ℤ, rdotZ c x = - (dot (dir e) x : ℝ) := by
    intro x
    simp only [hcdef, rdotZ, toReal, dot, Prod.fst_neg, Prod.snd_neg]
    push_cast
    ring
  have hlt : ∀ ν ∈ S, rdotZ c ν < 0 := by
    intro ν hν
    rw [hconv]
    have : (0 : ℤ) < dot (dir e) ν := by rw [dot_dir_left]; exact hSpos ν hν
    have : (0 : ℝ) < (dot (dir e) ν : ℝ) := by exact_mod_cast this
    linarith
  obtain ⟨ν', hν'S, hmax⟩ := S.exists_max_image (rkey c) hSne
  refine ⟨ν', hν'S, fun μ hμ hcontra => ?_⟩
  have hkey : rkey c μ ≤ rkey c ν' := hmax μ hμ
  have hiff := rkey_le_iff (c := c) (u := μ) (w := ν') (by
    intro hz; apply hdirne
    have h1 : (dir e).1 = 0 := by
      have := congrArg Prod.fst hz
      simpa [hcdef, toReal] using this
    have h2 : (dir e).2 = 0 := by
      have := congrArg Prod.snd hz
      simpa [hcdef, toReal] using this
    exact Prod.ext h1 h2) (hlt μ hμ) (hlt ν' hν'S)
  have h0le : (0 : ℤ) ≤ det μ ν' := hiff.mp hkey
  have hneg : det μ ν' = - det ν' μ := det_skew μ ν'
  omega

/-! ## §2. The chain-sum theorem, part (D)

`blueprint/LEAF-HSUPP.md`, §2(D). `Arc T ν₀ n := {ν ∈ E T | 0 < det ν₀ ν ∧ 0 < det ν n}`,
the edges of `T` strictly between `ν₀` and `n` in counter-clockwise order. -/

variable {faceStart faceLen}

/-- `Arc T ν₀ n`, as a `Finset`. -/
noncomputable def Arc (hfin : T.Finite) (ν₀ n : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  (finite_E_of_finite hfin).toFinset.filter (fun ν => 0 < det ν₀ ν ∧ 0 < det ν n)

theorem mem_Arc {hfin : T.Finite} {ν₀ n ν : ℤ × ℤ} :
    ν ∈ Arc hfin ν₀ n ↔ ν ∈ E T ∧ 0 < det ν₀ ν ∧ 0 < det ν n := by
  classical
  unfold Arc
  rw [Finset.mem_filter, (finite_E_of_finite hfin).mem_toFinset]

variable
  (hadjV : ∀ ν ν', ν ∈ E T → ν' ∈ E T → 0 < det ν ν' →
    (∀ μ ∈ E T, ¬ (0 < det ν μ ∧ 0 < det μ ν')) →
    faceStart T ν + (faceLen T ν : ℤ) • dir ν = faceStart T ν')
  (htrans : ∀ e a b c : ℤ × ℤ, 0 < dot e a → 0 < dot e b → 0 < dot e c →
    0 < det a b → 0 < det b c → 0 < det a c)

include hadjV htrans in
theorem chain_ccw_aux (hfin : T.Finite) :
    ∀ k : ℕ, ∀ ν₀ n : ℤ × ℤ, ν₀ ∈ E T → n ∈ E T → 0 < det ν₀ n →
      (Arc hfin ν₀ n).card = k →
      faceStart T n - faceStart T ν₀ =
        (faceLen T ν₀ : ℤ) • dir ν₀ + ∑ ν ∈ Arc hfin ν₀ n, (faceLen T ν : ℤ) • dir ν := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro ν₀ n hν₀ hn hpos hcard
    by_cases hempty : Arc hfin ν₀ n = ∅
    · -- base case: `ν₀`, `n` are fan-adjacent.
      rw [hempty, Finset.sum_empty, add_zero]
      have hadjcond : ∀ μ ∈ E T, ¬ (0 < det ν₀ μ ∧ 0 < det μ n) := by
        intro μ hμ ⟨h1, h2⟩
        have : μ ∈ Arc hfin ν₀ n := mem_Arc.mpr ⟨hμ, h1, h2⟩
        rw [hempty] at this
        exact absurd this (Finset.notMem_empty μ)
      have heq := hadjV ν₀ n hν₀ hn hpos hadjcond
      rw [← heq]; abel
    · -- inductive case: peel off the `det`-maximal element of `Arc hfin ν₀ n`.
      have hSne : (Arc hfin ν₀ n).Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
      have hSpos : ∀ ν ∈ Arc hfin ν₀ n, 0 < det ν₀ ν := fun ν hν => (mem_Arc.mp hν).2.1
      have hν₀ne : ν₀ ≠ 0 := (mem_E_iff.mp hν₀).1.ne_zero
      obtain ⟨ν', hν'S, hν'max⟩ := exists_max_det hν₀ne hSpos hSne
      obtain ⟨hν'mem, hν'ν₀, hν'detn⟩ := mem_Arc.mp hν'S
      have hadjcond : ∀ μ ∈ E T, ¬ (0 < det ν' μ ∧ 0 < det μ n) := by
        intro μ hμ ⟨h1, h2⟩
        have h0 : 0 < det ν₀ μ :=
          htrans (-dir n) ν₀ ν' μ
            (by rw [dot_neg_dir]; exact hpos)
            (by rw [dot_neg_dir]; exact hν'detn)
            (by rw [dot_neg_dir]; exact h2)
            hν'ν₀ h1
        have : μ ∈ Arc hfin ν₀ n := mem_Arc.mpr ⟨hμ, h0, h2⟩
        exact hν'max μ this h1
      have hstep := hadjV ν' n hν'mem hn hν'detn hadjcond
      -- `Arc hfin ν₀ n = insert ν' (Arc hfin ν₀ ν')`
      have hnotmem : ν' ∉ Arc hfin ν₀ ν' := by
        intro hmem
        have := (mem_Arc.mp hmem).2.2
        rw [det_self] at this
        exact absurd this (lt_irrefl 0)
      have hsplit : Arc hfin ν₀ n = insert ν' (Arc hfin ν₀ ν') := by
        ext μ
        simp only [Finset.mem_insert]
        constructor
        · intro hμ
          obtain ⟨hμmem, hμν₀, hμn⟩ := mem_Arc.mp hμ
          by_cases hμν' : μ = ν'
          · exact Or.inl hμν'
          · refine Or.inr (mem_Arc.mpr ⟨hμmem, hμν₀, ?_⟩)
            have hnotgt : ¬ (0 < det ν' μ) := hν'max μ hμ
            have hle : det ν' μ ≤ 0 := not_lt.mp hnotgt
            have hne0 : det ν' μ ≠ 0 := by
              intro hz
              obtain ⟨hprimν', -⟩ := mem_E_iff.mp hν'mem
              obtain ⟨hprimμ, -⟩ := mem_E_iff.mp hμmem
              rcases eq_or_neg_of_prim_of_det_eq_zero hprimν' hprimμ hz with heqn | heqn
              · exact hμν' heqn
              · have hneg : det ν₀ μ = - det ν₀ ν' := by
                  rw [heqn]; simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
                omega
            have hlt : det ν' μ < 0 := lt_of_le_of_ne hle hne0
            have hskew : det μ ν' = - det ν' μ := det_skew μ ν'
            omega
        · rintro (rfl | hμ)
          · exact hν'S
          · obtain ⟨hμmem, hμν₀, hμν'⟩ := mem_Arc.mp hμ
            refine mem_Arc.mpr ⟨hμmem, hμν₀, ?_⟩
            exact htrans (dir ν₀) μ ν' n
              (by rw [dot_dir_left]; exact hμν₀)
              (by rw [dot_dir_left]; exact hν'ν₀)
              (by rw [dot_dir_left]; exact hpos)
              hμν' hν'detn
      have hcardlt : (Arc hfin ν₀ ν').card < k := by
        have : (Arc hfin ν₀ n).card = (Arc hfin ν₀ ν').card + 1 := by
          rw [hsplit, Finset.card_insert_of_notMem hnotmem]
        omega
      have hih := ih (Arc hfin ν₀ ν').card hcardlt ν₀ ν' hν₀ hν'mem hν'ν₀ rfl
      have hsum : ∑ ν ∈ Arc hfin ν₀ n, (faceLen T ν : ℤ) • dir ν =
          (faceLen T ν' : ℤ) • dir ν' + ∑ ν ∈ Arc hfin ν₀ ν', (faceLen T ν : ℤ) • dir ν := by
        rw [hsplit, Finset.sum_insert hnotmem]
      rw [hsum]
      have hgoal2 : faceStart T n - faceStart T ν₀ =
          (faceStart T ν' - faceStart T ν₀) + (faceLen T ν' : ℤ) • dir ν' := by
        rw [← hstep]; abel
      rw [hgoal2, hih]
      abel

include hadjV htrans in
/-- **`chain_ccw`**, `blueprint/LEAF-HSUPP.md`, §2(D), counter-clockwise case:
for `ν₀, n ∈ E T` with `0 < det ν₀ n`, the vector from `faceStart T ν₀` to `faceStart T n`
is the sum of the direction vectors of every edge strictly between them (counted with
lattice length), starting with `ν₀`'s own edge. -/
theorem chain_ccw (hfin : T.Finite) {ν₀ n : ℤ × ℤ} (hν₀ : ν₀ ∈ E T) (hn : n ∈ E T)
    (hpos : 0 < det ν₀ n) :
    faceStart T n - faceStart T ν₀ =
      (faceLen T ν₀ : ℤ) • dir ν₀ +
        ∑ ν ∈ (finite_E_of_finite hfin).toFinset.filter (fun ν => 0 < det ν₀ ν ∧ 0 < det ν n),
          (faceLen T ν : ℤ) • dir ν :=
  chain_ccw_aux hadjV htrans hfin _ ν₀ n hν₀ hn hpos rfl

omit hadjV htrans in
/-- `dot n (dir ν) = det ν n`: the identity `blueprint/LEAF-HSUPP.md`, §0 records, needed to
turn the vector chain identity into a scalar (support-value) one. -/
theorem dot_dir_right (ν n : ℤ × ℤ) : dot n (dir ν) = det ν n := dot_dir_gen ν n

omit hadjV htrans in
theorem dot_sum (s : Finset (ℤ × ℤ)) (f : ℤ × ℤ → ℤ × ℤ) (n : ℤ × ℤ) :
    dot n (∑ ν ∈ s, f ν) = ∑ ν ∈ s, dot n (f ν) := by
  classical
  induction s using Finset.induction with
  | empty => simp [dot]
  | insert a s ha ih => rw [Finset.sum_insert ha, dot_add, ih, Finset.sum_insert ha]

omit hadjV htrans in
theorem dot_zsmul_right (n g : ℤ × ℤ) (c : ℤ) : dot n (c • g) = c * dot n g := by
  rw [dot_comm, dot_smul, dot_comm]

variable (hseg : ∀ ν ∈ E T, face T ν =
  {z | ∃ t : ℕ, t ≤ faceLen T ν ∧ z = faceStart T ν + (t : ℤ) • dir ν})

include hseg in
theorem faceStart_mem_face {n : ℤ × ℤ} (hn : n ∈ E T) : faceStart T n ∈ face T n := by
  rw [hseg n hn]
  exact ⟨0, Nat.zero_le _, by simp⟩

include hseg in
theorem suppVal_faceStart {n : ℤ × ℤ} (hn : n ∈ E T) : suppVal T n = dot n (faceStart T n) :=
  suppVal_eq (faceStart_mem_face hseg hn)

include hadjV htrans hseg in
/-- **`chain_ccw_scalar`**: the scalar (support-value) form of `chain_ccw`, obtained by
pairing both sides with `n` and using `suppVal T n = dot n (faceStart T n)`. Every summand
on the right is `≥ 0` (it is `(faceLen T ν : ℤ) * det ν n` for `ν` with `0 < det ν n`). -/
theorem chain_ccw_scalar (hfin : T.Finite) {ν₀ n : ℤ × ℤ} (hν₀ : ν₀ ∈ E T) (hn : n ∈ E T)
    (hpos : 0 < det ν₀ n) :
    suppVal T n - dot n (faceStart T ν₀) =
      (faceLen T ν₀ : ℤ) * det ν₀ n +
        ∑ ν ∈ (finite_E_of_finite hfin).toFinset.filter (fun ν => 0 < det ν₀ ν ∧ 0 < det ν n),
          (faceLen T ν : ℤ) * det ν n := by
  have hv := chain_ccw hadjV htrans hfin hν₀ hn hpos
  have hs := suppVal_faceStart hseg hn
  have hd : dot n (faceStart T n) - dot n (faceStart T ν₀)
      = dot n (faceStart T n - faceStart T ν₀) := (dot_sub n _ _).symm
  rw [hs, hd, hv, dot_add, dot_zsmul_right, dot_dir_right, dot_sum]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [dot_zsmul_right, dot_dir_right]

/-! ## §3. The clockwise case: a relabelling of `chain_ccw` -/

include hadjV htrans in
/-- **`chain_cw`**, `blueprint/LEAF-HSUPP.md`, §2(D), clockwise case: for `n, ν₀ ∈ E T` with
`0 < det n ν₀`, obtained from `chain_ccw` by swapping the roles of `ν₀` and `n`. -/
theorem chain_cw (hfin : T.Finite) {ν₀ n : ℤ × ℤ} (hν₀ : ν₀ ∈ E T) (hn : n ∈ E T)
    (hpos : 0 < det n ν₀) :
    faceStart T ν₀ - (faceStart T n + (faceLen T n : ℤ) • dir n) =
      ∑ ν ∈ (finite_E_of_finite hfin).toFinset.filter (fun ν => 0 < det ν ν₀ ∧ 0 < det n ν),
        (faceLen T ν : ℤ) • dir ν := by
  have hv := chain_ccw hadjV htrans hfin hn hν₀ hpos
  have hset : (finite_E_of_finite hfin).toFinset.filter (fun ν => 0 < det n ν ∧ 0 < det ν ν₀) =
      (finite_E_of_finite hfin).toFinset.filter (fun ν => 0 < det ν ν₀ ∧ 0 < det n ν) := by
    apply Finset.filter_congr
    intro ν _
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [hset] at hv
  have hv2 : faceStart T ν₀ - faceStart T n - (faceLen T n : ℤ) • dir n =
      ∑ ν ∈ (finite_E_of_finite hfin).toFinset.filter (fun ν => 0 < det ν ν₀ ∧ 0 < det n ν),
        (faceLen T ν : ℤ) • dir ν := by
    rw [hv]; abel
  rw [← hv2]; abel

include hadjV htrans hseg in
/-- **`chain_cw_scalar`**: the scalar form of `chain_cw`. -/
theorem chain_cw_scalar (hfin : T.Finite) {ν₀ n : ℤ × ℤ} (hν₀ : ν₀ ∈ E T) (hn : n ∈ E T)
    (hpos : 0 < det n ν₀) :
    suppVal T n - dot n (faceStart T ν₀) =
      ∑ ν ∈ (finite_E_of_finite hfin).toFinset.filter (fun ν => 0 < det ν ν₀ ∧ 0 < det n ν),
        (faceLen T ν : ℤ) * det n ν := by
  have hv := chain_cw hadjV htrans hfin hν₀ hn hpos
  have hs := suppVal_faceStart hseg hn
  set S := ∑ ν ∈ (finite_E_of_finite hfin).toFinset.filter (fun ν => 0 < det ν ν₀ ∧ 0 < det n ν),
      (faceLen T ν : ℤ) • dir ν with hSdef
  have hgn : faceStart T ν₀ - faceStart T n = (faceLen T n : ℤ) • dir n + S := by
    rw [← hv]; abel
  have h1 : dot n (faceStart T ν₀) - dot n (faceStart T n)
      = dot n ((faceLen T n : ℤ) • dir n) + dot n S := by
    rw [← dot_add, ← dot_sub, hgn]
  rw [dot_zsmul_right, dot_dir_right, det_self, mul_zero, zero_add] at h1
  have h2 : dot n S =
      ∑ ν ∈ (finite_E_of_finite hfin).toFinset.filter (fun ν => 0 < det ν ν₀ ∧ 0 < det n ν),
        (faceLen T ν : ℤ) * det ν n := by
    rw [hSdef, dot_sum]
    exact Finset.sum_congr rfl fun ν _ => by rw [dot_zsmul_right, dot_dir_right]
  rw [h2] at h1
  have hgoal : dot n (faceStart T n) - dot n (faceStart T ν₀) =
      -(∑ ν ∈ (finite_E_of_finite hfin).toFinset.filter (fun ν => 0 < det ν ν₀ ∧ 0 < det n ν),
          (faceLen T ν : ℤ) * det ν n) := by linarith [h1]
  rw [hs, hgoal, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun ν _ => by rw [det_skew n ν]; ring

/-! ## §4. Instantiation against `lane-hsupp`'s landed `Nivat.External.Colle.PolyChain`

`Nivat.PolyChain.adjacent_shared_vertex` (A), `Nivat.PolyChain.face_eq_segment` (B) and
`Nivat.PolyChain.det_pos_trans` (C) discharge `hadjV`/`hseg`/`htrans` for
`faceStart := Nivat.PolyChain.faceStart`, `faceLen := Nivat.PolyChain.faceLen`, given
`T.Finite` and `IsLatticeConvexRegion T`. -/

theorem hadjV_real {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hlc : IsLatticeConvexRegion T) :
    ∀ ν ν', ν ∈ E T → ν' ∈ E T → 0 < det ν ν' →
      (∀ μ ∈ E T, ¬ (0 < det ν μ ∧ 0 < det μ ν')) →
      Nivat.PolyChain.faceStart T ν + (Nivat.PolyChain.faceLen T ν : ℤ) • dir ν =
        Nivat.PolyChain.faceStart T ν' :=
  fun ν ν' hν hν' hpos hadj => Nivat.PolyChain.adjacent_shared_vertex hfin hlc hν hν' hpos hadj

theorem htrans_real : ∀ e a b c : ℤ × ℤ, 0 < dot e a → 0 < dot e b → 0 < dot e c →
    0 < det a b → 0 < det b c → 0 < det a c :=
  fun _ _ _ _ ha hb hc hab hbc => Nivat.PolyChain.det_pos_trans ha hb hc hab hbc

theorem hseg_real {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hlc : IsLatticeConvexRegion T) :
    ∀ ν ∈ E T, face T ν =
      {z | ∃ t : ℕ, t ≤ Nivat.PolyChain.faceLen T ν ∧
        z = Nivat.PolyChain.faceStart T ν + (t : ℤ) • dir ν} :=
  fun ν hν => Nivat.PolyChain.face_eq_segment hlc hfin hν

/-- **`chain_ccw_final`**: `chain_ccw` instantiated against the real `Nivat.PolyChain`
data, hypothesis-free beyond `T.Finite` / `IsLatticeConvexRegion T`. -/
theorem chain_ccw_final {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hlc : IsLatticeConvexRegion T)
    {ν₀ n : ℤ × ℤ} (hν₀ : ν₀ ∈ E T) (hn : n ∈ E T) (hpos : 0 < det ν₀ n) :
    Nivat.PolyChain.faceStart T n - Nivat.PolyChain.faceStart T ν₀ =
      (Nivat.PolyChain.faceLen T ν₀ : ℤ) • dir ν₀ +
        ∑ ν ∈ (finite_E_of_finite hfin).toFinset.filter (fun ν => 0 < det ν₀ ν ∧ 0 < det ν n),
          (Nivat.PolyChain.faceLen T ν : ℤ) • dir ν :=
  chain_ccw (hadjV_real hfin hlc) htrans_real hfin hν₀ hn hpos

/-- **`chain_ccw_scalar_final`**: `chain_ccw_scalar` instantiated against the real
`Nivat.PolyChain` data. -/
theorem chain_ccw_scalar_final {T : Set (ℤ × ℤ)} (hfin : T.Finite)
    (hlc : IsLatticeConvexRegion T) {ν₀ n : ℤ × ℤ} (hν₀ : ν₀ ∈ E T) (hn : n ∈ E T)
    (hpos : 0 < det ν₀ n) :
    suppVal T n - dot n (Nivat.PolyChain.faceStart T ν₀) =
      (Nivat.PolyChain.faceLen T ν₀ : ℤ) * det ν₀ n +
        ∑ ν ∈ (finite_E_of_finite hfin).toFinset.filter (fun ν => 0 < det ν₀ ν ∧ 0 < det ν n),
          (Nivat.PolyChain.faceLen T ν : ℤ) * det ν n :=
  chain_ccw_scalar (hadjV_real hfin hlc) htrans_real (hseg_real hfin hlc) hfin hν₀ hn hpos

/-- **`chain_cw_final`**: `chain_cw` instantiated against the real `Nivat.PolyChain` data. -/
theorem chain_cw_final {T : Set (ℤ × ℤ)} (hfin : T.Finite) (hlc : IsLatticeConvexRegion T)
    {ν₀ n : ℤ × ℤ} (hν₀ : ν₀ ∈ E T) (hn : n ∈ E T) (hpos : 0 < det n ν₀) :
    Nivat.PolyChain.faceStart T ν₀ -
        (Nivat.PolyChain.faceStart T n + (Nivat.PolyChain.faceLen T n : ℤ) • dir n) =
      ∑ ν ∈ (finite_E_of_finite hfin).toFinset.filter (fun ν => 0 < det ν ν₀ ∧ 0 < det n ν),
        (Nivat.PolyChain.faceLen T ν : ℤ) • dir ν :=
  chain_cw (hadjV_real hfin hlc) htrans_real hfin hν₀ hn hpos

/-- **`chain_cw_scalar_final`**: `chain_cw_scalar` instantiated against the real
`Nivat.PolyChain` data. -/
theorem chain_cw_scalar_final {T : Set (ℤ × ℤ)} (hfin : T.Finite)
    (hlc : IsLatticeConvexRegion T) {ν₀ n : ℤ × ℤ} (hν₀ : ν₀ ∈ E T) (hn : n ∈ E T)
    (hpos : 0 < det n ν₀) :
    suppVal T n - dot n (Nivat.PolyChain.faceStart T ν₀) =
      ∑ ν ∈ (finite_E_of_finite hfin).toFinset.filter (fun ν => 0 < det ν ν₀ ∧ 0 < det n ν),
        (Nivat.PolyChain.faceLen T ν : ℤ) * det n ν :=
  chain_cw_scalar (hadjV_real hfin hlc) htrans_real (hseg_real hfin hlc) hfin hν₀ hn hpos

#print axioms Nivat.PolyChainSum.exists_max_det
#print axioms Nivat.PolyChainSum.chain_ccw_final
#print axioms Nivat.PolyChainSum.chain_ccw_scalar_final
#print axioms Nivat.PolyChainSum.chain_cw_final
#print axioms Nivat.PolyChainSum.chain_cw_scalar_final
