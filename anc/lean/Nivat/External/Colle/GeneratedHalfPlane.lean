import Nivat.External.Colle.Generating

/-! # Unique continuation from a generated half-plane

If one site of a finite generating window uniquely minimizes the normal
projection, its local rule extends half-plane agreement one uniform shell
at a time. No assumption on the alphabet or finiteness of its range is
needed. This is the unique-continuation step in Colle Lemma 2.3.
-/

namespace Nivat.Colle

/-- A finite family of positive reals has a positive common lower bound.
The empty family is allowed. -/
private theorem exists_pos_le_of_finset_pos {ι : Type*} (F : Finset ι)
    (r : ι → ℝ) (hr : ∀ b ∈ F, 0 < r b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ b ∈ F, δ ≤ r b := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a F ha ih =>
    obtain ⟨δ, hδ, hb⟩ := ih (fun b hb => hr b (Finset.mem_insert_of_mem hb))
    refine ⟨min δ (r a), lt_min hδ (hr a (Finset.mem_insert_self ..)), ?_⟩
    intro b hbF
    rcases Finset.mem_insert.mp hbF with rfl | hbF
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hb b hbF)

/-- Agreement on a half-plane determines an orbit-closure member if a
generating window has a unique point of least normal projection.
The half-plane convention here is `c ≤ inner2 w z`. -/
theorem eq_of_halfPlane_of_generatesAt {A : Type*} {ξ x y : Config A}
    (hx : x ∈ orbitClosure ξ) (hy : y ∈ orbitClosure ξ)
    {S : Finset (ℤ × ℤ)} {a : ℤ × ℤ} (hgen : GeneratesAt ξ S a)
    {w : ℝ × ℝ} {c : ℝ}
    (hmin : ∀ b ∈ S.erase a, inner2 w a < inner2 w b)
    (hagree : ∀ z : ℤ × ℤ, c ≤ inner2 w z → x z = y z) : x = y := by
  obtain ⟨δ, hδ, hbound⟩ := exists_pos_le_of_finset_pos (S.erase a)
    (fun b => inner2 w b - inner2 w a) (fun b hb => sub_pos.mpr (hmin b hb))
  have hstep (d : ℝ) (hd : ∀ z : ℤ × ℤ, d ≤ inner2 w z → x z = y z) :
      ∀ z : ℤ × ℤ, d - δ ≤ inner2 w z → x z = y z := by
    intro z hz
    have hlocal : ∀ b ∈ S.erase a, T (z - a) x b = T (z - a) y b := by
      intro b hb
      apply hd
      simp only [sub_eq_add_neg, inner2_add, inner2_neg]
      have hb' := hbound b hb
      linarith
    have h := hgen.2 _ (T_mem_of_mem_orbitClosure hx (z - a))
      _ (T_mem_of_mem_orbitClosure hy (z - a)) hlocal
    simpa only [T, show a + (z - a) = z by abel] using h
  have hshell (n : ℕ) :
      ∀ z : ℤ × ℤ, c - (n : ℝ) * δ ≤ inner2 w z → x z = y z := by
    induction n with
    | zero => simpa only [Nat.cast_zero, zero_mul, sub_zero] using hagree
    | succ n ih =>
      simpa only [Nat.cast_succ, add_mul, one_mul, sub_sub] using
        hstep (c - (n : ℝ) * δ) ih
  funext z
  obtain ⟨n, hn⟩ := exists_nat_gt ((c - inner2 w z) / δ)
  have hn' : c - inner2 w z < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp hn
  exact hshell n z (by linarith)

end Nivat.Colle
