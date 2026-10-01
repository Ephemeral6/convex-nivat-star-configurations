/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.LatticeEdges

/-!
# Work towards `exists_chainData` (Colle §3)

Status: the target theorem `Nivat.ColleReg.exists_chainData` is **not** proved here.
See the report at the end of this file.  What is proved here, `sorry`-free and with no
new axioms, is convex-geometry content of Colle §3 that `LatticeEdges.lean` leaves open.
-/

namespace Nivat.ColleStep

open Nivat Nivat.LE2

/-! ## §1. `dot` is linear in its left argument -/

theorem dot_add_left (a b z : ℤ × ℤ) : dot (a + b) z = dot a z + dot b z := by
  simp only [dot, Prod.fst_add, Prod.snd_add]; ring

theorem dot_smul_left (w : ℤ) (a z : ℤ × ℤ) : dot (w • a) z = w * dot a z := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem dot_sum_left {ι : Type*} (s : Finset ι) (f : ι → ℤ × ℤ) (z : ℤ × ℤ) :
    dot (∑ i ∈ s, f i) z = ∑ i ∈ s, dot (f i) z := by
  classical
  induction s using Finset.induction with
  | empty => simp [dot]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, dot_add_left, ih]

/-! ## §2. A set on which two independent linear forms are bounded is finite -/

/-- If two lattice vectors `a`, `b` are linearly independent and both `dot a` and `dot b`
are bounded above and below on `T`, then `T` is finite. -/
theorem finite_of_dot_bounded {T : Set (ℤ × ℤ)} {a b : ℤ × ℤ} (hdet : det a b ≠ 0)
    {pa qa pb qb : ℤ}
    (ha : ∀ z ∈ T, pa ≤ dot a z ∧ dot a z ≤ qa)
    (hb : ∀ z ∈ T, pb ≤ dot b z ∧ dot b z ≤ qb) : T.Finite := by
  have hinj : Set.InjOn (fun z : ℤ × ℤ => ((dot a z, dot b z) : ℤ × ℤ)) T := by
    intro z _ z' _ h
    have h1 : dot a z = dot a z' := congrArg Prod.fst h
    have h2 : dot b z = dot b z' := congrArg Prod.snd h
    have e1 : det a b * (z.1 - z'.1) = 0 := by
      simp only [dot] at h1 h2
      simp only [det]
      linear_combination b.2 * h1 - a.2 * h2
    have e2 : det a b * (z.2 - z'.2) = 0 := by
      simp only [dot] at h1 h2
      simp only [det]
      linear_combination a.1 * h2 - b.1 * h1
    have f1 : z.1 = z'.1 := by
      rcases mul_eq_zero.mp e1 with h | h
      · exact absurd h hdet
      · omega
    have f2 : z.2 = z'.2 := by
      rcases mul_eq_zero.mp e2 with h | h
      · exact absurd h hdet
      · omega
    exact Prod.ext f1 f2
  refine Set.Finite.of_finite_image ?_ hinj
  refine Set.Finite.subset (Set.finite_Icc ((pa, pb) : ℤ × ℤ) ((qa, qb) : ℤ × ℤ)) ?_
  rintro _ ⟨z, hz, rfl⟩
  exact Set.mem_Icc.mpr ⟨⟨(ha z hz).1, (hb z hz).1⟩, ⟨(ha z hz).2, (hb z hz).2⟩⟩

/-! ## §3. An `E(𝒰)`-enveloped set is finite

Colle's Definition 3.2 forces `E(𝒯) = E(𝒰)`, so an enveloped set has *exactly* the edge
normals of the window.  When those normals positively span the plane — which is what
`∑ i, w i • n i = 0` with all `w i > 0` records — every one of the corresponding linear
forms is bounded on `𝒯` in **both** directions, and two independent ones pin `𝒯` inside a
box.  `LatticeEdges.lean` leaves this finiteness open ("the classification
results one really wants"). -/

/-- A face of `T` in the direction `n` bounds `dot n` above on `T`. -/
theorem dot_le_of_face_nonempty {T : Set (ℤ × ℤ)} {n : ℤ × ℤ} (h : (face T n).Nonempty) :
    ∃ q : ℤ, ∀ z ∈ T, dot n z ≤ q := by
  obtain ⟨z₀, hz₀⟩ := h
  exact ⟨dot n z₀, fun z hz => hz₀.2 z hz⟩

/-- The lower bound that a positive vanishing combination of bounded-above forms produces. -/
theorem exists_dot_lower_bound {T : Set (ℤ × ℤ)} {k : ℕ} {n : Fin k → ℤ × ℤ} {w : Fin k → ℤ}
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i • n i = 0)
    {c : Fin k → ℤ} (hc : ∀ i, ∀ z ∈ T, dot (n i) z ≤ c i) (j : Fin k) :
    ∃ p : ℤ, ∀ z ∈ T, p ≤ dot (n j) z := by
  classical
  set M : ℤ := ∑ i, w i * c i with hM
  refine ⟨-|w j * c j - M|, fun z hz => ?_⟩
  have hzero : ∑ i, w i * dot (n i) z = 0 := by
    have := dot_sum_left Finset.univ (fun i => w i • n i) z
    rw [hsum] at this
    simpa only [dot_smul_left, dot_zero_left] using this.symm
  -- split off the `j`-th term
  have hsplit : w j * dot (n j) z + ∑ i ∈ Finset.univ.erase j, w i * dot (n i) z = 0 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at hzero
    exact hzero
  have hle : ∑ i ∈ Finset.univ.erase j, w i * dot (n i) z
      ≤ ∑ i ∈ Finset.univ.erase j, w i * c i := by
    refine Finset.sum_le_sum ?_
    intro i _
    exact mul_le_mul_of_nonneg_left (hc i z hz) (le_of_lt (hw i))
  have hMsplit : M = w j * c j + ∑ i ∈ Finset.univ.erase j, w i * c i := by
    rw [hM, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  have hbound : w j * c j - M ≤ w j * dot (n j) z := by
    have : w j * dot (n j) z = -∑ i ∈ Finset.univ.erase j, w i * dot (n i) z := by omega
    rw [this, hMsplit]
    omega
  -- convert to a bound on `dot (n j) z` itself, using `1 ≤ w j`
  set d : ℤ := dot (n j) z with hd
  by_cases h : 0 ≤ d
  · have : (0 : ℤ) ≤ |w j * c j - M| := abs_nonneg _
    omega
  · have h' : d ≤ 0 := le_of_lt (lt_of_not_ge h)
    have h1 : (1 : ℤ) ≤ w j := hw j
    have : w j * d ≤ 1 * d := by
      exact mul_le_mul_of_nonpos_right h1 h'
    have habs : w j * c j - M ≤ |w j * c j - M| := le_abs_self _
    have habs2 : -|w j * c j - M| ≤ w j * c j - M := neg_abs_le _
    omega

/-- **An `E(𝒰)`-enveloped set is finite**, when the edge normals of `𝒰` contain a positively
spanning family with two independent members.  This is the shape in which Colle's
Definition 3.2 forces the sets `B_i`, `A_i`, `Â_i` of the §3 chain to be finite. -/
theorem finite_of_enveloped {U T : Set (ℤ × ℤ)} (hU : (E U).Finite) (h : Enveloped U T)
    {k : ℕ} {n : Fin k → ℤ × ℤ} {w : Fin k → ℤ} (hw : ∀ i, 0 < w i)
    (hsum : ∑ i, w i • n i = 0) (hmem : ∀ i, n i ∈ E U)
    {i j : Fin k} (hdet : det (n i) (n j) ≠ 0) : T.Finite := by
  classical
  have hE : E T = E U := Enveloped.E_eq hU h
  have hface : ∀ l, (face T (n l)).Nonempty := by
    intro l
    have : n l ∈ E T := by rw [hE]; exact hmem l
    exact this.2.nonempty
  have hupper : ∀ l, ∃ q : ℤ, ∀ z ∈ T, dot (n l) z ≤ q := fun l =>
    dot_le_of_face_nonempty (hface l)
  choose c hc using hupper
  obtain ⟨pi, hpi⟩ := exists_dot_lower_bound (T := T) hw hsum hc i
  obtain ⟨pj, hpj⟩ := exists_dot_lower_bound (T := T) hw hsum hc j
  exact finite_of_dot_bounded hdet (fun z hz => ⟨hpi z hz, hc i z hz⟩)
    (fun z hz => ⟨hpj z hz, hc j z hz⟩)

/-- Instantiation at a non-degenerate lattice box: **an `E(box p q)`-enveloped set is
finite.**  This is what pins `B i`, `A i`, `Â i` down once `Env` is `EnvOf ↑S`. -/
theorem finite_of_envOf_box {p q : ℤ × ℤ} (hp : p.1 < q.1) (hq : p.2 < q.2)
    {T : Set (ℤ × ℤ)} (h : EnvOf (box p q) T) : T.Finite := by
  refine finite_of_enveloped (U := box p q) (by rw [E_box hp hq]; exact Set.toFinite _) h
    (n := ![((1 : ℤ), (0 : ℤ)), (-1, 0), (0, 1), (0, -1)]) (w := fun _ => 1)
    (fun _ => one_pos) (by decide) ?_ (i := 0) (j := 2) (by decide)
  intro i
  rw [E_box hp hq]
  fin_cases i <;> simp

/-- The same for the unit square, the shape in which `ColleRegion`'s `winS` appears. -/
theorem finite_of_envOf_sq1 {T : Set (ℤ × ℤ)} (h : EnvOf sq1 T) : T.Finite :=
  finite_of_envOf_box (p := (0, 0)) (q := (1, 1)) (by norm_num) (by norm_num) h

/-! ## §4. The half-strip `H_{sq1}((1,0))` -/

theorem mem_halfStrip_e1 {z : ℤ × ℤ} :
    z ∈ halfStrip sq1 ((1 : ℤ), (0 : ℤ)) ↔ 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.2 ≤ 1 := by
  constructor
  · rintro ⟨b, hb, t, rfl⟩
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
    have ht : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      mul_one, mul_zero, add_zero]
    simp only at hb1 hb3 hb4
    exact ⟨by omega, hb3, hb4⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(0, z.2), ⟨le_rfl, by norm_num, h2, h3⟩, z.1.toNat, ?_⟩
    have : ((z.1.toNat : ℤ)) = z.1 := Int.toNat_of_nonneg h1
    apply Prod.ext <;> simp [this]

/-! ## §5. Colle's item (iv) is not available verbatim under `Nivat.LE2.Enveloped`

Colle, Definition 3.2, asks `𝒯` to be a **convex** set with `E(𝒯) = E(𝒰)` and each face of
`𝒯` at least as long as the corresponding face of `𝒰`.  `Nivat.LE2.Enveloped` keeps the two
edge conditions and drops convexity.  This section shows the drop is not harmless at the
step `ChainData.maximalHat` records, namely Colle's item (iv):

> "let `Â_i` be a **maximal** `E(S_φ)`-enveloped subset of the half-strip on which `η`
> agrees with the translate of `x_per`".

Take `𝒰 = B = sq1`, chain direction `v = (1,0)`, and let `η` disagree with `x_per` along the
whole wall `{z | z.1 = 5}` — a wall, not a point, which is the configuration the source uses
and which `Lemma35Wiring.chainB` exploits.  Then **no** `E(sq1)`-enveloped subset of
`H_{sq1}((1,0))` avoiding that wall is maximal: any one of them is strictly contained in
another.  The escape is the comb `combSet N` below, which hops over the wall; a convex set
containing `sq1` and reaching `z.1 = N > 5` could not.

### What this does and does not say

It is a statement about one explicit family, and that is deliberate.  It does **not** refute
`ChainData.maximalHat`: `Lemma35Wiring.chainB` is a complete `sorry`-free `ChainData` with
`Env = EnvOf sq1`, so `maximalHat` is satisfiable.  What it does say is that the *reason*
`maximalHat` holds there cannot be "Colle's item (iv)", because item (iv) fails here at the
same `𝒰`.  Any proof of `maximalHat` must therefore use structure this family lacks — the
finiteness and `i`-dependence of `B i`, the shift `kk i`, or a genuinely thin agreement set —
and not the mere existence of maximal enveloped sets.  That is the crux of
`ColleReg.exists_chainData`, and it is where the present file stops. -/

/-- The "comb": two rows of the half-strip, truncated at `N`, with the wall `z.1 = 5`
punched out.  It has exactly the four edge normals of `sq1` (`E_combSet`) but it is **not**
convex (`not_isLatticeConvexRegion_combSet`), hence **not** `E(sq1)`-enveloped
(`not_envOf_combSet`).  It is the standing witness that the edge data of Definition 3.2 does
not imply its convexity clause. -/
def combSet (N : ℤ) : Set (ℤ × ℤ) :=
  {z | 0 ≤ z.1 ∧ z.1 ≤ N ∧ (z.2 = 0 ∨ z.2 = 1) ∧ z.1 ≠ 5}

theorem mem_combSet {N : ℤ} {z : ℤ × ℤ} :
    z ∈ combSet N ↔ 0 ≤ z.1 ∧ z.1 ≤ N ∧ (z.2 = 0 ∨ z.2 = 1) ∧ z.1 ≠ 5 := Iff.rfl

/-- In every non-axis direction the comb exposes a single corner, so it has no edge there. -/
theorem face_combSet_of_ne_zero {N : ℤ} (hN : 7 ≤ N) {n : ℤ × ℤ}
    (h1 : n.1 ≠ 0) (h2 : n.2 ≠ 0) :
    face (combSet N) n ⊆ {(endp n.1 0 N, endp n.2 0 1)} := by
  have hN0 : (0 : ℤ) ≤ N := by omega
  have hC : (endp n.1 0 N, endp n.2 0 1) ∈ combSet N := by
    refine ⟨(endp_mem hN0).1, (endp_mem hN0).2, ?_, ?_⟩
    · show endp n.2 0 1 = 0 ∨ endp n.2 0 1 = 1
      unfold endp; split <;> simp
    · show endp n.1 0 N ≠ 5
      unfold endp; split <;> omega
  have hmax : ∀ z ∈ combSet N, dot n z ≤ dot n (endp n.1 0 N, endp n.2 0 1) := by
    rintro z ⟨a1, a2, a3, _⟩
    simp only [dot]
    refine add_le_add (mul_le_endp n.1 a1 a2) (mul_le_endp n.2 ?_ ?_) <;> omega
  rintro z ⟨hz, hzm⟩
  have hle := hmax z hz
  have hge := hzm _ hC
  obtain ⟨a1, a2, a3, _⟩ := hz
  have e1 := mul_le_endp n.1 a1 a2
  have e2 : n.2 * z.2 ≤ n.2 * endp n.2 0 1 := by
    refine mul_le_endp n.2 ?_ ?_ <;> omega
  simp only [dot] at hle hge
  have f1 : n.1 * z.1 = n.1 * endp n.1 0 N := by linarith
  have f2 : n.2 * z.2 = n.2 * endp n.2 0 1 := by linarith
  exact Set.mem_singleton_iff.mpr
    (Prod.ext (mul_left_cancel₀ h1 f1) (mul_left_cancel₀ h2 f2))

theorem E_combSet {N : ℤ} (hN : 7 ≤ N) :
    E (combSet N) = {(1, 0), (-1, 0), (0, 1), (0, -1)} := by
  have hr0 : ((N : ℤ), (0 : ℤ)) ∈ face (combSet N) (1, 0) :=
    ⟨⟨by omega, le_rfl, Or.inl rfl, by omega⟩, fun y hy => by
      simp only [dot_e1]; exact hy.2.1⟩
  have hr1 : ((N : ℤ), (1 : ℤ)) ∈ face (combSet N) (1, 0) :=
    ⟨⟨by omega, le_rfl, Or.inr rfl, by omega⟩, fun y hy => by
      simp only [dot_e1]; exact hy.2.1⟩
  have hl0 : ((0 : ℤ), (0 : ℤ)) ∈ face (combSet N) (-1, 0) :=
    ⟨⟨le_rfl, by omega, Or.inl rfl, by omega⟩, fun y hy => by
      simp only [dot_e1']; have := hy.1; omega⟩
  have hl1 : ((0 : ℤ), (1 : ℤ)) ∈ face (combSet N) (-1, 0) :=
    ⟨⟨le_rfl, by omega, Or.inr rfl, by omega⟩, fun y hy => by
      simp only [dot_e1']; have := hy.1; omega⟩
  have ht0 : ((0 : ℤ), (1 : ℤ)) ∈ face (combSet N) (0, 1) :=
    ⟨⟨le_rfl, by omega, Or.inr rfl, by omega⟩, fun y hy => by
      simp only [dot_e2]; have := hy.2.2.1; omega⟩
  have ht1 : ((1 : ℤ), (1 : ℤ)) ∈ face (combSet N) (0, 1) :=
    ⟨⟨by omega, by omega, Or.inr rfl, by omega⟩, fun y hy => by
      simp only [dot_e2]; have := hy.2.2.1; omega⟩
  have hb0 : ((0 : ℤ), (0 : ℤ)) ∈ face (combSet N) (0, -1) :=
    ⟨⟨le_rfl, by omega, Or.inl rfl, by omega⟩, fun y hy => by
      simp only [dot_e2']; have := hy.2.2.1; omega⟩
  have hb1 : ((1 : ℤ), (0 : ℤ)) ∈ face (combSet N) (0, -1) :=
    ⟨⟨by omega, by omega, Or.inl rfl, by omega⟩, fun y hy => by
      simp only [dot_e2']; have := hy.2.2.1; omega⟩
  ext n
  constructor
  · rintro ⟨hprim, hnt⟩
    by_cases h1 : n.1 = 0
    · rcases prim_eq_of_fst_eq_zero hprim h1 with rfl | rfl <;> simp
    · by_cases h2 : n.2 = 0
      · rcases prim_eq_of_snd_eq_zero hprim h2 with rfl | rfl <;> simp
      · exact absurd (hnt.mono (face_combSet_of_ne_zero hN h1 h2)) Set.not_nontrivial_singleton
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨by decide, ⟨_, hr0, _, hr1, by intro h; rw [Prod.ext_iff] at h; omega⟩⟩
    · exact ⟨by decide, ⟨_, hl0, _, hl1, by intro h; rw [Prod.ext_iff] at h; omega⟩⟩
    · exact ⟨by decide, ⟨_, ht0, _, ht1, by intro h; rw [Prod.ext_iff] at h; omega⟩⟩
    · exact ⟨by decide, ⟨_, hb0, _, hb1, by intro h; rw [Prod.ext_iff] at h; omega⟩⟩

/-- **`combSet N` is not lattice-convex.**  It contains `(4,0)` and `(6,0)` but its defining
condition punches out the column `z.1 = 5`, which contains their midpoint.

Same argument, different witness, as `Nivat.ColleStep.not_isLatticeConvexRegion_bad`. -/
theorem not_isLatticeConvexRegion_combSet {N : ℤ} (hN : 7 ≤ N) :
    ¬ IsLatticeConvexRegion (combSet N) := by
  rintro ⟨C, hconv, -, heq⟩
  have h4 : toReal ((4 : ℤ), (0 : ℤ)) ∈ C := by
    have hm : ((4 : ℤ), (0 : ℤ)) ∈ combSet N :=
      ⟨by omega, by omega, Or.inl rfl, by omega⟩
    rw [heq] at hm; exact hm
  have h6 : toReal ((6 : ℤ), (0 : ℤ)) ∈ C := by
    have hm : ((6 : ℤ), (0 : ℤ)) ∈ combSet N :=
      ⟨by omega, by omega, Or.inl rfl, by omega⟩
    rw [heq] at hm; exact hm
  have hmid : toReal ((5 : ℤ), (0 : ℤ)) ∈ C := by
    have hA : ((1 : ℝ) / 2) • toReal ((4 : ℤ), (0 : ℤ))
        + ((1 : ℝ) / 2) • toReal ((6 : ℤ), (0 : ℤ)) ∈ C :=
      hconv h4 h6 (by norm_num) (by norm_num) (by norm_num)
    have hAeq : ((1 : ℝ) / 2) • toReal ((4 : ℤ), (0 : ℤ))
        + ((1 : ℝ) / 2) • toReal ((6 : ℤ), (0 : ℤ)) = toReal ((5 : ℤ), (0 : ℤ)) := by
      simp only [toReal, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.mk.injEq]
      norm_num
    rwa [hAeq] at hA
  have hmem : ((5 : ℤ), (0 : ℤ)) ∈ combSet N := by rw [heq]; exact hmid
  exact (mem_combSet.mp hmem).2.2.2 rfl

/-- **`combSet N` is not `E(sq1)`-enveloped.**

This is the corrected form of a theorem `envOf_combSet` that stood here until 2026-09-16 and
asserted the *opposite*, with its convexity obligation left `sorry`.  That obligation could
never have been discharged: `EnvOf sq1` unfolds to `Enveloped sq1`, which carries
`IsLatticeConvexRegion` through `WeaklyEnveloped`, and `not_isLatticeConvexRegion_combSet`
above refutes exactly that.

The edge computation the old proof did supply — `E_combSet` and the four `encard` bounds — is
correct and is kept above; it simply does not add up to `Enveloped` once Definition 3.2's
convexity clause is present. -/
theorem not_envOf_combSet {N : ℤ} (hN : 7 ≤ N) : ¬ EnvOf sq1 (combSet N) :=
  fun e => not_isLatticeConvexRegion_combSet hN e.1.1


theorem sq1_subset_combSet {N : ℤ} (hN : 7 ≤ N) : sq1 ⊆ combSet N := by
  rintro z ⟨a1, a2, a3, a4⟩
  exact ⟨a1, by omega, by omega, by omega⟩

theorem combSet_subset_halfStrip {N : ℤ} : combSet N ⊆ halfStrip sq1 ((1 : ℤ), (0 : ℤ)) := by
  rintro z ⟨a1, _, a3, _⟩
  exact mem_halfStrip_e1.mpr ⟨a1, by omega, by omega⟩

/-! ### Withdrawn 2026-09-16: `no_maximal_enveloped_avoiding_wall`

A theorem stood here asserting that **Colle's item (iv) is false** — that every
`E(sq1)`-enveloped subset of the half-strip `H_{sq1}((1,0))` avoiding the wall `{z | z.1 = 5}`
is strictly contained in another, so the family in which Colle picks a maximum has no top and
`ChainData.maximalHat` cannot be discharged by transcribing the source.

**That claim is retracted.**  Its entire content was the strictly larger set it produced,
namely `combSet N`, supplied by `envOf_combSet` — and `envOf_combSet` is false
(`not_envOf_combSet` above).  The theorem's own docstring named the reason without drawing the
consequence: *"The obstruction is the missing convexity clause of Definition 3.2."*  That
clause is no longer missing; `ea5bbc5` restored it.  Under the repaired `Enveloped`, `combSet N`
is not enveloped at all, so it never met the hypothesis it was supposed to refute, and the
family of enveloped wall-avoiding subsets is *not* shown to be unbounded.

This is the same failure mode as the retracted `region_latticeConvex` refutation
(`Step_LatConvex.lean`, §2-§3) and as `enveloped_bad`: a "refutation" whose witness fails the
definition it is quantified over.  See `CLAUDE.md`, "已撤回的结论".

Whether Colle's item (iv) is transcribable is therefore **reopened**, not settled either way.
What survives is only that the family is nonempty: -/

/-- **The family of Colle's item (iv) is nonempty** — there is an `E(sq1)`-enveloped subset of
the half-strip avoiding the wall `{z | z.1 = 5}`.

The witness used to be `combSet 7`, which is not enveloped.  `sq1` itself works and is
convex, so this survives the retraction above.  It is weaker than the withdrawn theorem in
exactly the way it should be: it says the family has members, not that it has no maximum. -/
theorem exists_enveloped_avoiding_wall :
    ∃ T : Set (ℤ × ℤ), EnvOf sq1 T ∧ sq1 ⊆ T ∧
      T ⊆ halfStrip sq1 ((1 : ℤ), (0 : ℤ)) ∧ (∀ z ∈ T, z.1 ≠ 5) :=
  ⟨sq1, enveloped_refl sq1 isLatticeConvexRegion_sq1, subset_rfl,
    subset_halfStrip sq1 _, fun z hz => by obtain ⟨a1, a2, a3, a4⟩ := hz; omega⟩


/-! ## Status

Proved here, `sorry`-free, no new `axiom`, no `native_decide`:

* §1–§2 linearity of `dot` in its left slot, and `finite_of_dot_bounded`;
* §3 `finite_of_enveloped`: an `E(𝒰)`-enveloped set is **finite** whenever the edge normals
  of `𝒰` contain a positively spanning family with two independent members, with the
  instantiations `finite_of_envOf_box` and `finite_of_envOf_sq1`.  `LatticeEdges.lean` lists
  this under "not done here";
* §4 the membership criterion for `H_{sq1}((1,0))`;
* §5 `not_isLatticeConvexRegion_combSet` / `not_envOf_combSet`: the comb has exactly the four
  edge normals of `sq1` (`E_combSet`) and the required face cardinalities, yet is **not**
  `E(sq1)`-enveloped, because it is not convex.  So the edge data of Definition 3.2 does not
  imply its convexity clause;
* §5 `exists_enveloped_avoiding_wall`: the family of Colle's item (iv) is nonempty.

**Retracted 2026-09-16**: §5 previously claimed Colle's item (iv) is *false* as formalized
(`no_maximal_enveloped_avoiding_wall`).  That claim rested on `combSet N` being enveloped,
which `not_envOf_combSet` now refutes.  See the §5 withdrawal note.

## `Nivat.ColleReg.exists_chainData` is NOT proved here

Two independent blockers, both measured against the tree rather than guessed.

1. **The periodic witness.**  The conclusion demands `xper ∈ orbitClosure ξ` together with
   `p ∈ Per xper`, `p ≠ 0`: a genuinely periodic element of the orbit closure.  In Colle
   this is not part of §3 at all — §3.1 gets it from *Kari–Moutot Theorem 1.9* plus the
   *Boyle–Lind theorem* ("all oriented lines through the origin are one-sided expansive
   directions on `Orb(x_per)`, which due to the Boyle–Lind Theorem means that `x_per` is
   fully periodic").  In this repository the only two routes to that statement are
   `Nivat.colle_doublyPeriodic` (`Nivat/Section8/External.lean`, an **axiom**) and
   `Nivat.Colle.theorem114` (`Theorem114.lean`), which depends transitively on two `sorry`s,
   `Nivat.KM17.lemma17` (`KMLemma17.lean`) and
   `Nivat.Colle.doublyPeriodic_of_orbitClosure_witness` (`Theorem114.lean`).  So
   `exists_chainData` strictly contains open content and cannot be closed here without
   either weakening it (forbidden) or importing an axiom (forbidden).

2. **`maximalHat`.**  Even granting the witness, the 19th field of `ChainData` is the crux.
   §5 used to claim it cannot come from Colle's item (iv) "once `Enveloped` has dropped the
   convexity clause of Definition 3.2", and prescribed two repairs: restore convexity to
   `Nivat.LE2.Enveloped`, or derive `maximalHat` from the `i`-dependence of `B i` and the
   shift `kk i`.  **The first repair has since landed** (`ea5bbc5`), and it dissolved the
   §5 obstruction rather than confirming it: with convexity back, the comb is not enveloped,
   so it witnesses nothing about maxima.  Whether item (iv) transcribes is now **open**, and
   nothing here decides it.  `maximalHat` remains undischarged. -/

end Nivat.ColleStep
