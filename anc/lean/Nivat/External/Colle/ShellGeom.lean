/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.ShellGen
import Nivat.External.Colle.ShellLine
import Nivat.External.Colle.LowComplexityWindow

/-!
# `RegionLayers.gen` for Collé's shells, reduced to statements about `Â_∞` and `S_φ`

`ShellLine.lean` split the layers; `ShellGen.lean` swept the new line.  This file discharges
the two remaining *combinatorial* obligations of `Nivat.Colle37.gen_of_line` — the lattice
convexity of `S_φ ∖ {a}` at the two endpoints of the sweep edge, and the "off the line"
membership — and assembles `gen_of_shell`, which produces the `gen` field for
`Nivat.MaxEnv.shell`, the faithful transcription of `b3_colle2.txt:440`.

## Orientation of `n`

`shell A v n c ε = reachSet A v ∩ {c - ε ≤ ⟪n, ·⟫}` (`shell_eq_reach_inter`), so `ℓ_J` sits
at `⟪n, ·⟫ = c` and the region hangs on the side where `⟪n, ·⟫` *decreases*.  The new line of
layer `ε + 1` is `⟪n, ·⟫ = c - ε - 1`, the one farthest from `ℓ_J`.  For a translate
`z + (b - a)` of a new site to land in the *previous* layer we therefore need
`⟪n, b - a⟫ ≥ 1`: the sweep edge of `S_φ` must be its `⟪n, ·⟫`-**minimal** face, and `a`, `a'`
are its two endpoints.  That is why `gen_of_shell` passes `-n` to the lex test below.

## What is left after this file

`gen_of_shell` consumes only geometry, no induction:

* `hedge`, `hedge'`, `hlex`, `hlex'` — that the `ℓ_J`-parallel face of the zonotope `S_φ` is
  `⟪n, ·⟫`-minimal, that `a, a'` are its endpoints, and that the `r + 1` lattice points of
  that face are `a, a + d, …, a + r·d = a'`;
* `hline`, `hstab`, `hsplit` — that the bottom line of `Â_∞^{(ε+1)}` is the
  half-line `{z₀ + k·d : k ≥ L}` and that `Â_∞` absorbs the translations `b - a`, i.e. that
  `S_φ - a` lies in the recession cone of the `(ℓ_ι, ℓ_J)`-region `Â_∞^{(ε+1)}`.

⚠ **`hstab'` deleted 2026-09-19.**  Until then `gen_of_shell` also took the mirror hypothesis
at the other endpoint, `hstab' : ∀ b ∈ S, 1 ≤ dot n (b - a') → ∀ k ≥ L, z₀ + k•d + (b - a') ∈
reachSet A v`, and fed it to `gen_of_line`'s `hup`.  It is derivable: the face hypotheses force
`a' = a + j•d` with `j ≤ r` (`run_of_face`), so the `a'`-translate at site `k` *is* the
`a`-translate at site `k - j`, and `ray_up` (`ShellGen.lean:75`) only ever reads `hup` at
`k > M + r ≥ L + r`, where `k - j ≥ L`.  `gen_of_line_late` restates the sweep with exactly
that range; `gen_of_shell` then manufactures `hstab'` itself.  The deletion is what lets the
bundle field `ChainDataGeom.bottom` (`ChainGeom.lean`) drop its conjunct (iv), which the kernel
had shown to force `a = a'` (`ShellMink.ChainDataGeom.a_eq_a'`) and, in the guarded form landed
earlier that day, to be false on Collé's own `m = 2` shape
(`tmp/Abottom_noIV.lean`, `not_guardedIV_quad_sq1` — receipt, not landed).

## Main results

* `latticeConvex_erase_of_lexExtreme` — erasing a strictly lexicographically extreme point
  of a lattice-convex finite set keeps it lattice-convex.
* `offLine_mem_shell` — a translate with positive `n`-height drops a new site into the
  previous layer.
* `run_of_face` — the two endpoints of the sweep edge differ by `j•d`, `j ≤ r`.
* `gen_of_line_late` — `Nivat.Colle37.gen_of_line` with `hup` restricted to `L + r < k`.
* `gen_of_shell` — the `RegionLayers.gen` field for `Nivat.MaxEnv.shell`.
-/

namespace Nivat.Colle37Geom

open Nivat Nivat.LE2 Nivat.Colle

/-- **Erasing a lexicographically extreme point preserves lattice convexity.**

`a` is assumed strictly largest in `S` for the order "first `⟪n, ·⟫`, then `⟪d, ·⟫`".  The
separating functional is the real perturbation `n + δ·d` with `δ = 1/(M+1)` small enough that
it cannot overturn a strict gap in `⟪n, ·⟫`; then `S.erase a` is an open real half-plane cut
of `S`, and `Nivat.Colle.latticeConvex_filter_inner2_lt` applies.

This is the vertex fact `Nivat.Colle37.gen_of_line` needs, in the only form the application
can supply it: the two endpoints of an edge of a zonotope are lex-extreme for (outer normal,
edge direction), and no convex-geometry development is required. -/
theorem latticeConvex_erase_of_lexExtreme {S : Finset (ℤ × ℤ)} (hS : LatticeConvex S)
    {a n d : ℤ × ℤ}
    (hlex : ∀ b ∈ S.erase a,
      dot n b < dot n a ∨ (dot n b = dot n a ∧ dot d b < dot d a)) :
    LatticeConvex (S.erase a) := by
  classical
  set M : ℕ := ∑ z ∈ S, (dot d z - dot d a).natAbs with hM
  set δ : ℝ := 1 / ((M : ℝ) + 1) with hδ
  have hMpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδM : δ * (M : ℝ) < 1 := by
    rw [hδ, div_mul_eq_mul_div, one_mul, div_lt_one hMpos]
    linarith
  set w : ℝ × ℝ := ((n.1 : ℝ) + δ * (d.1 : ℝ), (n.2 : ℝ) + δ * (d.2 : ℝ)) with hw
  have key : ∀ z : ℤ × ℤ, inner2 w z = (dot n z : ℝ) + δ * (dot d z : ℝ) := by
    intro z
    simp only [inner2, hw, dot]
    push_cast
    ring
  have hbound : ∀ b ∈ S, |(dot d b : ℝ) - (dot d a : ℝ)| ≤ (M : ℝ) := by
    intro b hb
    have h1 : (dot d b - dot d a).natAbs ≤ M := by
      rw [hM]
      exact Finset.single_le_sum (f := fun z => (dot d z - dot d a).natAbs)
        (fun _ _ => Nat.zero_le _) hb
    have h2 : |dot d b - dot d a| ≤ (M : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast h1
    have : |((dot d b - dot d a : ℤ) : ℝ)| ≤ ((M : ℤ) : ℝ) := by
      rw [← Int.cast_abs]; exact_mod_cast h2
    push_cast at this
    exact this
  have hlt : ∀ b ∈ S.erase a, inner2 w b < inner2 w a := by
    intro b hb
    have hbS : b ∈ S := Finset.mem_of_mem_erase hb
    rw [key, key]
    have hbd := hbound b hbS
    rw [abs_le] at hbd
    rcases hlex b hb with h | ⟨h1, h2⟩
    · have hn : (dot n b : ℝ) ≤ (dot n a : ℝ) - 1 := by
        have : dot n b ≤ dot n a - 1 := by omega
        exact_mod_cast this
      nlinarith [hbd.2, hδpos, hδM]
    · have hn : (dot n b : ℝ) = (dot n a : ℝ) := by exact_mod_cast h1
      have hdd : (dot d b : ℝ) ≤ (dot d a : ℝ) - 1 := by
        have : dot d b ≤ dot d a - 1 := by omega
        exact_mod_cast this
      nlinarith [hδpos]
  have hfilter : S.filter (fun z => inner2 w z < inner2 w a) = S.erase a := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hbS, hblt⟩
      refine ⟨?_, hbS⟩
      rintro rfl
      exact lt_irrefl _ hblt
    · rintro ⟨hba, hbS⟩
      exact ⟨hbS, hlt b (Finset.mem_erase.mpr ⟨hba, hbS⟩)⟩
  rw [← hfilter]
  exact latticeConvex_filter_inner2_lt hS w _

/-- **A translate with positive `n`-height drops a new site into the previous layer.**

`z` is on the bottom line of `Â_∞^{(ε+1)}` (`⟪n, z⟫ = c - ε - 1`).  If the swept set absorbs
`δ` and `⟪n, δ⟫ ≥ 1`, then `z + δ` is already in `Â_∞^{(ε)}`.  This is the second disjunct of
`Nivat.Colle37.genClosure_ray`'s `hdown`/`hup`. -/
theorem offLine_mem_shell {A : Set (ℤ × ℤ)} {v n : ℤ × ℤ} {c : ℤ} {ε : ℕ} {z δ : ℤ × ℤ}
    (hd : dot n z = c - (ε : ℤ) - 1)
    (hstab : z + δ ∈ MaxEnv.reachSet A v) (hh : 1 ≤ dot n δ) :
    z + δ ∈ MaxEnv.shell A v n c ε := by
  rw [MaxEnv.shell_eq_reach_inter]
  refine ⟨hstab, ?_⟩
  simp only [Set.mem_ofPred_eq, dot_add, hd]
  omega

open Nivat.Colle37 Nivat.MaxEnv

/-! ### The sweep reads `hup` only at `M + r < k`

`Nivat.Colle37.genClosure_ray` (`ShellGen.lean:104`) takes `hup`'s off-line clause for every
`k ≥ L`, but `ray_up` (`ShellGen.lean:75`) invokes its step only at `M + r < k`.  The two
theorems below restate the sweep with that range and are otherwise the same proofs. -/

/-- `Colle37.genClosure_ray` with `hup`'s off-line clause restricted to `M + r < k`. -/
theorem genClosure_ray_late {S : Finset (ℤ × ℤ)} {D : Set (ℤ × ℤ)} {a a' d z₀ : ℤ × ℤ}
    {r : ℕ} {L M : ℤ} (hLM : L ≤ M)
    (ha : a ∈ S) (ha' : a' ∈ S)
    (hconv : LatticeConvex (S.erase a)) (hconv' : LatticeConvex (S.erase a'))
    (hdown : ∀ b ∈ S.erase a,
        (∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ b = a + (j : ℤ) • d) ∨
          ∀ k : ℤ, L ≤ k → z₀ + k • d + (b - a) ∈ D)
    (hup : ∀ b ∈ S.erase a',
        (∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ b = a' - (j : ℤ) • d) ∨
          ∀ k : ℤ, M + (r : ℤ) < k → z₀ + k • d + (b - a') ∈ D)
    (hseed : ∀ k : ℤ, M ≤ k → k ≤ M + (r : ℤ) → z₀ + k • d ∈ D) :
    ∀ k : ℤ, L ≤ k → GenClosure S D (z₀ + k • d) := by
  have hbase : ∀ k : ℤ, L ≤ k → k ≤ M + (r : ℤ) → GenClosure S D (z₀ + k • d) := by
    refine ray_down (P := fun k => GenClosure S D (z₀ + k • d))
      (fun k h1 h2 => GenClosure.base (hseed k h1 h2)) ?_
    intro k hkL _ hlt
    have hkey : a + (z₀ + k • d - a) = z₀ + k • d := by abel
    rw [← hkey]
    refine GenClosure.step ha hconv ?_
    intro b hb
    rcases hdown b hb with ⟨j, hj1, hjr, rfl⟩ | hoff
    · have hshift : a + (j : ℤ) • d + (z₀ + k • d - a) = z₀ + (k + (j : ℤ)) • d := by
        rw [add_smul]; abel
      rw [hshift]
      exact hlt j hj1 hjr
    · have hshift : b + (z₀ + k • d - a) = z₀ + k • d + (b - a) := by abel
      rw [hshift]
      exact GenClosure.base (hoff k hkL)
  refine ray_up hLM hbase ?_
  intro k hk hlt
  have hkey : a' + (z₀ + k • d - a') = z₀ + k • d := by abel
  rw [← hkey]
  refine GenClosure.step ha' hconv' ?_
  intro b hb
  rcases hup b hb with ⟨j, hj1, hjr, rfl⟩ | hoff
  · have hshift : a' - (j : ℤ) • d + (z₀ + k • d - a') = z₀ + (k - (j : ℤ)) • d := by
      rw [sub_smul]; abel
    rw [hshift]
    exact hlt j hj1 hjr
  · have hshift : b + (z₀ + k • d - a') = z₀ + k • d + (b - a') := by abel
    rw [hshift]
    exact GenClosure.base (hoff k hk)

/-- `Colle37.gen_of_line` (`ShellGen.lean:203`) with `hup` restricted to `L + r < k`. -/
theorem gen_of_line_late {A : ℕ → Set (ℤ × ℤ)} {ε : ℕ} {S : Finset (ℤ × ℤ)}
    {d z₀ a a' : ℤ × ℤ} {r : ℕ} {L : ℤ}
    (hsplit : ∀ z ∈ A (ε + 1), z ∈ A ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • d)
    (hline : ∀ k : ℤ, L ≤ k → z₀ + k • d ∈ A (ε + 1))
    (ha : a ∈ S) (ha' : a' ∈ S)
    (hconv : LatticeConvex (S.erase a)) (hconv' : LatticeConvex (S.erase a'))
    (hdown : ∀ b ∈ S.erase a,
        (∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ b = a + (j : ℤ) • d) ∨
          ∀ k : ℤ, L ≤ k → z₀ + k • d + (b - a) ∈ A ε)
    (hup : ∀ b ∈ S.erase a',
        (∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ b = a' - (j : ℤ) • d) ∨
          ∀ k : ℤ, L + (r : ℤ) < k → z₀ + k • d + (b - a') ∈ A ε) :
    ∃ i M : ℕ, ∀ t : ℕ, M ≤ t → ∀ z ∈ A (ε + 1),
      GenClosure S (A ε ∪ (A (ε + 1) ∩ winS i ((t : ℤ) • d))) z := by
  refine ⟨lineRadius z₀ d r, L.toNat, ?_⟩
  intro t ht z hz
  have hLt : L ≤ (t : ℤ) := by omega
  rcases hsplit z hz with h | ⟨k, hkL, rfl⟩
  · exact GenClosure.base (Or.inl h)
  · refine genClosure_ray_late (M := (t : ℤ)) (r := r) hLt ha ha' hconv hconv' ?_ ?_ ?_ k hkL
    · intro b hb
      rcases hdown b hb with h | h
      · exact Or.inl h
      · exact Or.inr fun k hk => Or.inl (h k hk)
    · intro b hb
      rcases hup b hb with h | h
      · exact Or.inl h
      · exact Or.inr fun k hk => Or.inl (h k (by omega))
    · intro k h1 h2
      exact Or.inr ⟨hline k (le_trans hLt h1), mem_winS_lineRadius z₀ d r h1 h2⟩

/-! ### The two endpoints of the sweep edge differ by a run of `d` -/

/-- The two endpoints sit on one `n`-level (`hlex` + `hlex'`). -/
theorem dot_a_eq_a' {S : Finset (ℤ × ℤ)} {a a' n d : ℤ × ℤ} (ha : a ∈ S) (ha' : a' ∈ S)
    (hlex : ∀ b ∈ S.erase a,
      dot (-n) b < dot (-n) a ∨ (dot (-n) b = dot (-n) a ∧ dot (-d) b < dot (-d) a))
    (hlex' : ∀ b ∈ S.erase a',
      dot (-n) b < dot (-n) a' ∨ (dot (-n) b = dot (-n) a' ∧ dot d b < dot d a')) :
    dot n a = dot n a' := by
  rcases eq_or_ne a a' with rfl | hne
  · rfl
  · have h1 := hlex a' (Finset.mem_erase.mpr ⟨hne.symm, ha'⟩)
    have h2 := hlex' a (Finset.mem_erase.mpr ⟨hne, ha⟩)
    rw [dot_neg_left, dot_neg_left] at h1 h2
    omega

/-- **`a' = a + j • d` with `j ≤ r`**, from the face hypotheses alone (`j = 0` iff `a = a'`). -/
theorem run_of_face {S : Finset (ℤ × ℤ)} {a a' n d : ℤ × ℤ} {r : ℕ} (ha : a ∈ S) (ha' : a' ∈ S)
    (hlex : ∀ b ∈ S.erase a,
      dot (-n) b < dot (-n) a ∨ (dot (-n) b = dot (-n) a ∧ dot (-d) b < dot (-d) a))
    (hlex' : ∀ b ∈ S.erase a',
      dot (-n) b < dot (-n) a' ∨ (dot (-n) b = dot (-n) a' ∧ dot d b < dot d a'))
    (hedge : ∀ b ∈ S.erase a,
      (∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ b = a + (j : ℤ) • d) ∨ 1 ≤ dot n (b - a)) :
    ∃ j : ℕ, j ≤ r ∧ a' = a + (j : ℤ) • d := by
  rcases eq_or_ne a a' with rfl | hne
  · exact ⟨0, Nat.zero_le _, by simp⟩
  · have hlev := dot_a_eq_a' ha ha' hlex hlex'
    rcases hedge a' (Finset.mem_erase.mpr ⟨hne.symm, ha'⟩) with ⟨j, -, hjr, hj⟩ | h
    · exact ⟨j, hjr, hj⟩
    · rw [dot_sub] at h; omega

/-- **`Nivat.Colle37.RegionLayers.gen` for Collé's shells.**

The conclusion is literally the `gen` field with `A := shell A v n c`, `Sphi := S`, `v := d`.
Every hypothesis is a statement about the zonotope `S` or about the swept set `A`; no
induction and no window bookkeeping is left — `ShellGen.lean` constructs both the radius `i`
and the threshold `M`.

`hlex`/`hlex'` use `-n` because the sweep edge is the `⟪n, ·⟫`-**minimal** face of `S`; see
the module docstring.  `a` is its `d`-minimal endpoint and `a'` its `d`-maximal one, so `a`
is lex-max for `(-n, -d)` and `a'` is lex-max for `(-n, d)`.

Only the `a`-side absorption `hstab` is taken (2026-09-19; see the module docstring): the
`a'`-side instance the upward sweep needs at `k > L + r` is `hstab` at `k - j ≥ L`, where
`a' = a + j • d` by `run_of_face`. -/
theorem gen_of_shell
    {A : Set (ℤ × ℤ)} {v n : ℤ × ℤ} {c : ℤ} {ε : ℕ} {S : Finset (ℤ × ℤ)}
    {a a' d z₀ : ℤ × ℤ} {r : ℕ} {L : ℤ}
    (hS : LatticeConvex S) (ha : a ∈ S) (ha' : a' ∈ S)
    (hlex : ∀ b ∈ S.erase a,
      dot (-n) b < dot (-n) a ∨ (dot (-n) b = dot (-n) a ∧ dot (-d) b < dot (-d) a))
    (hlex' : ∀ b ∈ S.erase a',
      dot (-n) b < dot (-n) a' ∨ (dot (-n) b = dot (-n) a' ∧ dot d b < dot d a'))
    (hedge : ∀ b ∈ S.erase a,
      (∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ b = a + (j : ℤ) • d) ∨ 1 ≤ dot n (b - a))
    (hedge' : ∀ b ∈ S.erase a',
      (∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ b = a' - (j : ℤ) • d) ∨ 1 ≤ dot n (b - a'))
    (hdn : dot n d = 0) (hdz : dot n z₀ = c - (ε : ℤ) - 1)
    (hline : ∀ k : ℤ, L ≤ k → z₀ + k • d ∈ reachSet A v)
    (hstab : ∀ b ∈ S, 1 ≤ dot n (b - a) → ∀ k : ℤ, L ≤ k →
      z₀ + k • d + (b - a) ∈ reachSet A v)
    (hsplit : ∀ z ∈ shell A v n c (ε + 1),
      z ∈ shell A v n c ε ∨ ∃ k : ℤ, L ≤ k ∧ z = z₀ + k • d) :
    ∃ i M : ℕ, ∀ t : ℕ, M ≤ t → ∀ z ∈ shell A v n c (ε + 1),
      GenClosure S (shell A v n c ε ∪
        (shell A v n c (ε + 1) ∩ winS i ((t : ℤ) • d))) z := by
  have hheight : ∀ k : ℤ, dot n (z₀ + k • d) = c - (ε : ℤ) - 1 := by
    intro k
    have hs : dot n (k • d) = k * dot n d := by
      simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [dot_add, hs, hdn, hdz]; ring
  obtain ⟨j, hjr, hj⟩ := run_of_face ha ha' hlex hlex' hedge
  have hlev := dot_a_eq_a' ha ha' hlex hlex'
  -- the `a'`-side absorption, for `k > L + r`: the translate by `b - a'` of site `k` is the
  -- translate by `b - a` of site `k - j ≥ L`
  have hstab' : ∀ b ∈ S, 1 ≤ dot n (b - a') → ∀ k : ℤ, L + (r : ℤ) < k →
      z₀ + k • d + (b - a') ∈ reachSet A v := by
    intro b hb hoff k hk
    have hoff' : 1 ≤ dot n (b - a) := by rw [dot_sub] at hoff ⊢; omega
    have he : z₀ + k • d + (b - a') = z₀ + (k - (j : ℤ)) • d + (b - a) := by
      rw [hj, sub_smul]; abel
    rw [he]
    have hjr' : (j : ℤ) ≤ (r : ℤ) := by exact_mod_cast hjr
    exact hstab b hb hoff' _ (by omega)
  refine gen_of_line_late (z₀ := z₀) (d := d) (r := r) (L := L) hsplit ?_ ha ha'
    (latticeConvex_erase_of_lexExtreme hS hlex)
    (latticeConvex_erase_of_lexExtreme hS hlex') ?_ ?_
  · intro k hk
    rw [shell_eq_reach_inter]
    exact ⟨hline k hk, by simp only [Set.mem_ofPred_eq, hheight k]; omega⟩
  · intro b hb
    rcases hedge b hb with h | h
    · exact Or.inl h
    · refine Or.inr fun k hk => offLine_mem_shell (hheight k) ?_ h
      exact hstab b (Finset.mem_of_mem_erase hb) h k hk
  · intro b hb
    rcases hedge' b hb with h | h
    · exact Or.inl h
    · refine Or.inr fun k hk => offLine_mem_shell (hheight k) ?_ h
      exact hstab' b (Finset.mem_of_mem_erase hb) h k hk

end Nivat.Colle37Geom
