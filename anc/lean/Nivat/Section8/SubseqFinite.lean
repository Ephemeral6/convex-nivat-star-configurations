/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.PeriodCount

/-!
# Lemma 8.16, Step 1: the set of subsequential limits is finite

Let `G : ℤ² → α` over a finite alphabet `α` have the coarse period `k • v`, with `(v, u)` a
unimodular basis, and let `d` satisfy `δ := −π_v(d) > 0`.  If every element of
`Ω := subseqLimits G d` is doubly periodic, then `Ω` is finite.

This is Step 1 of the paper's Lemma 8.16 (p. 26).  A warning about its shape, because the
natural guess is wrong: the proof produces **no a priori bound on the trace**.  The paper argues
by contradiction — assume `Ω` infinite, extract `yₙ ∈ Ω` with `Tr(yₙ) → ∞`, pass to a limit
`θ ∈ Ω`, and only *then* put `P := Tr(θ)`.  The bound exists only once the contradiction is
complete, so "supply an explicit `P`" and "prove Step 1" are the same task, not two.

The heavy lifting lives in `Nivat.PeriodCount`:

* `finite_of_trace_le` — the easy half, `{y : Tr(y) ≤ P}` is finite for each `P`;
* `exists_bad_row_or_good` — the per-`n` trichotomy (no bad row / bad row left / bad row right);
* `false_of_infinite_left_bad_row`, `false_of_infinite_right_bad_row` — the core contradiction,
  in its two mirror-image cases.  The paper disposes of the second in one clause ("the case of
  finite `bₙ` being symmetric"), but it does not follow from the first by relabelling `ϖ ↦ -ϖ`,
  since negating `ϖ` also flips which side of the bad row the known-good interval lies on.

What this file adds is the top-level assembly: the three-way pigeonhole that feeds those three.

## Main results

* `Nivat.finite_subseqLimits_of_doublyPeriodic` — Step 1.  This is the entry point.
* `Nivat.finite_subseqLimits_of_right_bad_row` — the same statement, but taking the right-hand
  mirror of `false_of_infinite_left_bad_row` as an explicit hypothesis `hright` instead of
  calling it.  It carries the whole proof; the entry point is one application of it.  This
  version was written while `false_of_infinite_right_bad_row` was still pending, using the device
  `first_half_plane_dichotomy_of_sep` uses for its `hsep`, so that this file was `sorry`-free
  from the start; it is kept because `hright` isolates exactly what the assembly asks of the
  mirror, which is the cheapest way to re-audit that interface later.

One interface point worth recording, since the natural guess is again wrong.  The bad row `x`
handed out at `n := (N j : ℤ)`, `P₀ := π_v(ϖ)` satisfies only `(N j : ℤ) - π_v(ϖ) < x`, which is
*weaker* than `(N j : ℤ) < x`: rows `t` are certified good by the agreement of `θ` and `y (m j)`
on `BWin v u (N j)` only when `t` **and** `t + π_v(ϖ)` both lie in `[-(N j), N j]`, so the
extremal bad row can genuinely sit in `((N j) - π_v(ϖ), N j]`.  In exchange the good interval is
handed over in the combined form `[-(N j), x)`, obtained by splicing the trichotomy's own
`[(N j) - π_v(ϖ), x)` onto the agreement window `[-(N j), (N j) - π_v(ϖ)]`; that far edge is what
makes the shifted good interval's floor tend to `-∞` downstream.
-/

namespace Nivat

variable {α : Type*} [Finite α]

/-- **Lemma 8.16, Step 1**, conditional on the right-hand mirror of
`false_of_infinite_left_bad_row` (passed as `hright`).  For the unconditional statement, which
simply discharges `hright` with `false_of_infinite_right_bad_row`, see
`finite_subseqLimits_of_doublyPeriodic` below.

`Ω := subseqLimits G d` is finite.  By contradiction: if `Ω` were infinite then, since
`finite_of_trace_le` makes every trace-sublevel set of `Ω` finite, the trace is unbounded on
`Ω`, so we may pick `y j ∈ Ω` with `Tr(y j) > j`.  A diagonal extraction gives `θ ∈ Ω` agreeing
with `y (m n)` on the window `BWin v u n` for some `m n ≥ n`; `θ` is doubly periodic, so it has
a period `ϖ` with `π_v(ϖ) = Tr(θ) =: P > 0`.  Agreement on the window makes every row of
`[-n, n - P]` `ϖ`-good for `y (m n)`, so `exists_bad_row_or_good` applies: either `ϖ` is a
period of `y (m n)` outright — whence `Tr(y (m n)) ≤ P < n ≤ m n < Tr(y (m n))`, absurd — or
there is an extremal bad row on the left or on the right.  One of the two sides therefore occurs
for infinitely many `n`, and each is refuted: the left by `false_of_infinite_left_bad_row`, the
right by `hright`. -/
theorem finite_subseqLimits_of_right_bad_row {G : Config α} {v u d : ℤ × ℤ}
    (hvu : det v u = 1) {k : ℕ} (hk : 0 < k) (hper : ((k : ℤ) • v) ∈ Per G)
    (hd : 0 < -(pi v d)) (hlim : ∀ y ∈ subseqLimits G d, DoublyPeriodic y)
    (hright : ∀ w : ℕ → Config α, (∀ j, w j ∈ subseqLimits G d) →
      (∀ j, ((k : ℤ) • v) ∈ Per (w j)) → ∀ ϖ : ℤ × ℤ, 0 < pi v ϖ →
      ∀ N : ℕ → ℕ, (∀ j, j ≤ N j) → ∀ (M : ℕ → ℕ) (S : Set ℕ), S.Infinite →
      (∀ j ∈ S, ∃ x : ℤ, (N j : ℤ) - pi v ϖ < x ∧
        (∃ z, pi v z = x ∧ w (M j) (z + ϖ) ≠ w (M j) z) ∧
        (∀ t : ℤ, -(N j : ℤ) ≤ t → t < x → ∀ z, pi v z = t →
          w (M j) (z + ϖ) = w (M j) z)) → False) :
    (subseqLimits G d).Finite := by
  classical
  by_contra hinf
  have hv : Primitive v := Primitive_of_det_eq_one hvu
  -- **Step 0.**  Each trace-sublevel set of `Ω` is finite, so an infinite `Ω` has unbounded
  -- trace: for every `P` some element of `Ω` has trace exceeding `P`.
  have hunb : ∀ P : ℕ, ∃ y ∈ subseqLimits G d, P < trace v y := by
    intro P
    by_contra hb
    refine hinf ((finite_of_trace_le hvu hk P).subset ?_)
    intro w hw
    refine ⟨mem_Per_of_mem_subseqLimits hw hper, hlim w hw, ?_⟩
    by_contra hcon
    exact hb ⟨w, hw, by omega⟩
  choose y hyΩ hytr using hunb
  have hyper : ∀ j, ((k : ℤ) • v) ∈ Per (y j) :=
    fun j => mem_Per_of_mem_subseqLimits (hyΩ j) hper
  -- **Step 1.**  A limit point `θ` of the sequence, its trace `P`, and a period `ϖ` of `θ`
  -- realising that trace.
  obtain ⟨θ, hθΩ, hθagree⟩ := exists_mem_subseqLimits_agree y hyΩ
  have hθdp : DoublyPeriodic θ := hlim θ hθΩ
  have hθper : ((k : ℤ) • v) ∈ Per θ := mem_Per_of_mem_subseqLimits hθΩ hper
  obtain ⟨ϖ, hϖper, hϖeq⟩ := exists_mem_Per_pi_eq_trace hv hθdp
  have hPpos : 0 < trace v θ := trace_pos hv hθdp
  set P : ℕ := trace v θ with hPdef
  have hϖpos : 0 < pi v ϖ := by rw [hϖeq]; exact_mod_cast hPpos
  -- **Step 2.**  For each `n` an index `m n ≥ n` with `θ = y (m n)` on the window `B_n`.
  have hmex : ∀ n : ℕ, ∃ j, n ≤ j ∧ ∀ w ∈ BWin v u n, θ w = y j w :=
    fun n => hθagree (BWin v u n) n
  choose m hmle hmagree using hmex
  -- Agreement on the window propagates from the finitely many window points of a row to the
  -- whole row, since both configurations carry the coarse period `k • v`.
  have hrow : ∀ n : ℕ, k ≤ n → ∀ t : ℤ, |t| ≤ (n : ℤ) → ∀ z, pi v z = t → θ z = y (m n) z := by
    intro n hkn t ht z hz
    have hzdecomp : z = (det z u) • v + t • u := by
      have h := eq_smul_add_smul hvu z
      rwa [show det v z = pi v z from rfl, hz] at h
    have hres : θ ((det z u) • v + t • u) = y (m n) ((det z u) • v + t • u) :=
      eq_on_row_of_eq_on_BWin hk hθper (hyper (m n)) hkn ht (hmagree n) (det z u)
    rwa [← hzdecomp] at hres
  -- Hence every row of `[-n, n - π_v(ϖ)]` is `ϖ`-good for `y (m n)`: both `z` and `z + ϖ` then
  -- lie in rows on which `θ` and `y (m n)` agree, and `ϖ` is a period of `θ`.
  have hknown : ∀ n : ℕ, k ≤ n → ∀ t : ℤ, -(n : ℤ) ≤ t → t ≤ (n : ℤ) - pi v ϖ →
      ∀ z, pi v z = t → y (m n) (z + ϖ) = y (m n) z := by
    intro n hkn t ht1 ht2 z hz
    have habs1 : |t| ≤ (n : ℤ) := by rw [abs_le]; omega
    have hzϖ : pi v (z + ϖ) = t + pi v ϖ := by rw [pi_add, hz]
    have habs2 : |t + pi v ϖ| ≤ (n : ℤ) := by rw [abs_le]; omega
    have e1 : θ z = y (m n) z := hrow n hkn t habs1 z hz
    have e2 : θ (z + ϖ) = y (m n) (z + ϖ) := hrow n hkn (t + pi v ϖ) habs2 (z + ϖ) hzϖ
    rw [← e1, ← e2]
    exact Per.apply hϖper z
  -- **Step 3.**  For every `n` past `P` and past `k`, `y (m n)` has an extremal bad row on one
  -- side; the "no bad row" branch of the trichotomy is impossible, as it would cap the trace.
  have htri : ∀ n : ℕ, P < n → k ≤ n →
      (∃ x : ℤ, x < -(n : ℤ) ∧
        (∃ z, pi v z = x ∧ y (m n) (z + ϖ) ≠ y (m n) z) ∧
        ∀ t : ℤ, x < t → t ≤ (n : ℤ) - pi v ϖ → ∀ z, pi v z = t →
          y (m n) (z + ϖ) = y (m n) z) ∨
      (∃ x : ℤ, (n : ℤ) - pi v ϖ < x ∧
        (∃ z, pi v z = x ∧ y (m n) (z + ϖ) ≠ y (m n) z) ∧
        ∀ t : ℤ, -(n : ℤ) ≤ t → t < x → ∀ z, pi v z = t →
          y (m n) (z + ϖ) = y (m n) z) := by
    intro n hPn hkn
    have hPn' : (P : ℤ) < (n : ℤ) := by exact_mod_cast hPn
    have hnPle : -(n : ℤ) ≤ (n : ℤ) - pi v ϖ := by rw [hϖeq]; omega
    rcases exists_bad_row_or_good (y := y (m n)) (v := v) (ϖ := ϖ) (P₀ := pi v ϖ)
        (n := (n : ℤ)) hnPle (hknown n hkn) with hall | hleft | hrgt
    · exfalso
      have hϖmem : ϖ ∈ Per (y (m n)) := by
        rw [mem_Per_iff]; funext z; exact hall z
      have hmem : P ∈ traceSet v (y (m n)) := ⟨hPpos, ϖ, hϖmem, hϖeq⟩
      have hle : trace v (y (m n)) ≤ P := Nat.sInf_le hmem
      have hgt := hytr (m n)
      have hmn := hmle n
      omega
    · exact Or.inl hleft
    · right
      obtain ⟨x, hx1, hx2, hx3⟩ := hrgt
      refine ⟨x, hx1, hx2, fun t ht1 ht2 z hz => ?_⟩
      rcases le_or_gt ((n : ℤ) - pi v ϖ) t with h | h
      · exact hx3 t h ht2 z hz
      · exact hknown n hkn t ht1 h.le z hz
  -- **Step 4.**  One of the two sides occurs for infinitely many `n`; each is refuted.
  set L : Set ℕ := {n | (P < n ∧ k ≤ n) ∧ ∃ x : ℤ, x < -(n : ℤ) ∧
    (∃ z, pi v z = x ∧ y (m n) (z + ϖ) ≠ y (m n) z) ∧
    ∀ t : ℤ, x < t → t ≤ (n : ℤ) - pi v ϖ → ∀ z, pi v z = t →
      y (m n) (z + ϖ) = y (m n) z} with hLdef
  set R : Set ℕ := {n | (P < n ∧ k ≤ n) ∧ ∃ x : ℤ, (n : ℤ) - pi v ϖ < x ∧
    (∃ z, pi v z = x ∧ y (m n) (z + ϖ) ≠ y (m n) z) ∧
    ∀ t : ℤ, -(n : ℤ) ≤ t → t < x → ∀ z, pi v z = t →
      y (m n) (z + ϖ) = y (m n) z} with hRdef
  have hBinf : {n : ℕ | P < n ∧ k ≤ n}.Infinite := by
    apply Set.infinite_of_not_bddAbove
    rintro ⟨M, hM⟩
    have hmem : P + k + M + 1 ∈ {n : ℕ | P < n ∧ k ≤ n} := ⟨by omega, by omega⟩
    have := hM hmem
    omega
  have hcover : {n : ℕ | P < n ∧ k ≤ n} ⊆ L ∪ R := by
    intro n hn
    rcases htri n hn.1 hn.2 with h | h
    · exact Or.inl ⟨hn, h⟩
    · exact Or.inr ⟨hn, h⟩
  have hsplit : L.Infinite ∨ R.Infinite := by
    by_contra hc
    obtain ⟨h1, h2⟩ := not_or.mp hc
    rw [Set.not_infinite] at h1 h2
    exact hBinf ((h1.union h2).subset hcover)
  rcases hsplit with hLinf | hRinf
  · exact false_of_infinite_left_bad_row hvu hk hd hlim y hyΩ hyper hθΩ hθper hϖper hϖpos
      (N := fun n => n) (fun n => le_refl n) (m := m) hmagree hLinf (fun n hn => hn.2)
  · exact hright y hyΩ hyper ϖ hϖpos (fun n => n) (fun n => le_refl n) m R hRinf
      (fun n hn => hn.2)

/-- **Lemma 8.16, Step 1.**  If every subsequential limit of `(T^{nd} G)` is doubly periodic,
then there are only finitely many of them.

This is `finite_subseqLimits_of_right_bad_row` with its hypothesis `hright` discharged by
`false_of_infinite_right_bad_row`; see that theorem for the argument. -/
theorem finite_subseqLimits_of_doublyPeriodic {G : Config α} {v u d : ℤ × ℤ}
    (hvu : det v u = 1) {k : ℕ} (hk : 0 < k) (hper : ((k : ℤ) • v) ∈ Per G)
    (hd : 0 < -(pi v d)) (hlim : ∀ y ∈ subseqLimits G d, DoublyPeriodic y) :
    (subseqLimits G d).Finite :=
  finite_subseqLimits_of_right_bad_row hvu hk hper hd hlim
    (fun w hw hwper _ϖ hϖpos N hNmono M _S hS hbad =>
      false_of_infinite_right_bad_row hvu hk hd hlim w hw hwper hϖpos (N := N) hNmono
        (m := M) hS hbad)

end Nivat
