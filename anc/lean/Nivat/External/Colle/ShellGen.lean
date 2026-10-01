/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Nivat.External.Colle.Claim37

/-!
# The forcing order behind Collé's "we may enlarge" (`b3_colle2.txt:597`)

`Nivat.Colle37.RegionLayers.gen` asks that every site of `Â_∞^{(ε+1)}` lie in the
`S_φ`-generated closure of `Â_∞^{(ε)}` together with one far window `Q + t·v_{ℓ'}`.
`ShellLine.mem_shell_succ_iff` reduces this to the sites of a **single lattice line**
parallel to `ℓ_J`; this file supplies the induction that sweeps that line.

The line is parametrised by `k ↦ z₀ + k • d` with `d = v_{ℓ_J}`, and only the half-line
`k ≥ L` belongs to the region — the `ℓ_J`-edge of an `(ℓ_ι, ℓ_J)`-region is *semi-infinite*,
so every hypothesis below is restricted to `L ≤ k`.  Two vertices of `S_φ` drive the sweep,
the two endpoints of the edge of `S_φ` parallel to `ℓ_J`:

* `a`, the endpoint extreme in the `-d` direction, forces site `k` from sites
  `k+1, …, k+r` (its edge neighbours) plus sites strictly inside `Â_∞^{(ε)}`;
* `a'`, the endpoint extreme in the `+d` direction, forces site `k` from
  `k-1, …, k-r` plus sites strictly inside `Â_∞^{(ε)}`.

The seed is the finite block `[M, M+r]` of sites the window already covers.  `a` sweeps
downwards from it to `L`, `a'` upwards to `+∞`, so together they cover the half-line.  Both
directions are needed: the window `Q + t₀·v_{ℓ'}` is bounded, while the edge is not.

Nothing here is geometric: the two vertices and the two "off the line" clauses are
hypotheses.  The geometric statement that discharges them is that `S_φ - a` lies in the
recession cone of the `(ℓ_ι, ℓ_J)`-region `Â_∞^{(ε+1)}` (`b3_colle2.txt:440` asserts the
shell *is* such a region).

## Main results

* `ray_down`, `ray_up` — integer induction out of a block of `r+1` consecutive seeds.
* `genClosure_ray` — every site of the half-line is in `GenClosure S D`.
* `gen_of_line` — the `RegionLayers.gen` field itself, modulo the two geometric clauses.
-/

namespace Nivat.Colle37

open Nivat Nivat.LE2

/-- **Downward induction out of a seed block, stopping at `L`.**

`P` is known on the `r+1` consecutive integers `M, …, M+r`, and `P k` is forced by
`P (k+1), …, P (k+r)` as long as `L ≤ k`.  Then `P` holds on `[L, M+r]`. -/
theorem ray_down {P : ℤ → Prop} {L M : ℤ} {r : ℕ}
    (hseed : ∀ k : ℤ, M ≤ k → k ≤ M + (r : ℤ) → P k)
    (hstep : ∀ k : ℤ, L ≤ k → k < M →
      (∀ j : ℕ, 1 ≤ j → j ≤ r → P (k + (j : ℤ))) → P k) :
    ∀ k : ℤ, L ≤ k → k ≤ M + (r : ℤ) → P k := by
  have key : ∀ m : ℕ, ∀ k : ℤ, (M - k).toNat ≤ m → L ≤ k → k ≤ M + (r : ℤ) → P k := by
    intro m
    induction m with
    | zero => intro k hk _ hk2; exact hseed k (by omega) hk2
    | succ p ih =>
        intro k hk hkL hk2
        rcases le_or_gt M k with hMk | hMk
        · exact hseed k hMk hk2
        · refine hstep k hkL hMk fun j hj1 hjr => ih (k + (j : ℤ)) ?_ ?_ ?_
          · have h1 : (1 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj1
            omega
          · have h1 : (1 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj1
            omega
          · have h2 : (j : ℤ) ≤ (r : ℤ) := by exact_mod_cast hjr
            omega
  intro k hkL hk
  exact key (M - k).toNat k le_rfl hkL hk

/-- **Upward induction out of the same seed block.**

`P` is known on `[L, M+r]` and `P k` is forced by `P (k-1), …, P (k-r)`.  Then `P` holds on
`[L, ∞)`.  `L ≤ M` keeps the backward references inside the known range. -/
theorem ray_up {P : ℤ → Prop} {L M : ℤ} {r : ℕ} (hLM : L ≤ M)
    (hbase : ∀ k : ℤ, L ≤ k → k ≤ M + (r : ℤ) → P k)
    (hstep : ∀ k : ℤ, M + (r : ℤ) < k → (∀ j : ℕ, 1 ≤ j → j ≤ r → P (k - (j : ℤ))) → P k) :
    ∀ k : ℤ, L ≤ k → P k := by
  have key : ∀ m : ℕ, ∀ k : ℤ, (k - (M + (r : ℤ))).toNat ≤ m → L ≤ k → P k := by
    intro m
    induction m with
    | zero => intro k hk hkL; exact hbase k hkL (by omega)
    | succ p ih =>
        intro k hk hkL
        rcases le_or_gt k (M + (r : ℤ)) with h | h
        · exact hbase k hkL h
        · refine hstep k h fun j hj1 hjr => ih (k - (j : ℤ)) ?_ ?_
          · have h1 : (1 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj1
            omega
          · have h2 : (j : ℤ) ≤ (r : ℤ) := by exact_mod_cast hjr
            omega
  intro k hkL
  exact key (k - (M + (r : ℤ))).toNat k le_rfl hkL

/-- **The half-line is `S`-generated from `D`.**

`d` is the direction of the edge of `S` along which the sweep runs, `a` and `a'` are its two
endpoints, `r` bounds the number of lattice steps along that edge, and `M, …, M+r` is the
block of sites already in `D` (Collé's `Â^{(ε+1)}_∞ ∩ (Q + t₀ v_{ℓ'})`).

The second disjunct of `hdown`/`hup` is the "off the line" case: the translate `b - a` of a
generator that is *not* on the sweep edge lands the site strictly inside `D` — in the
application, inside `Â_∞^{(ε)}`, because `b - a` has positive height over `ℓ_J`. -/
theorem genClosure_ray {S : Finset (ℤ × ℤ)} {D : Set (ℤ × ℤ)} {a a' d z₀ : ℤ × ℤ}
    {r : ℕ} {L M : ℤ} (hLM : L ≤ M)
    (ha : a ∈ S) (ha' : a' ∈ S)
    (hconv : LatticeConvex (S.erase a)) (hconv' : LatticeConvex (S.erase a'))
    (hdown : ∀ b ∈ S.erase a,
        (∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ b = a + (j : ℤ) • d) ∨
          ∀ k : ℤ, L ≤ k → z₀ + k • d + (b - a) ∈ D)
    (hup : ∀ b ∈ S.erase a',
        (∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ b = a' - (j : ℤ) • d) ∨
          ∀ k : ℤ, L ≤ k → z₀ + k • d + (b - a') ∈ D)
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
  have hkL : L ≤ k := by omega
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
    exact GenClosure.base (hoff k hkL)

/-! ## The window that carries the seed block

Collé's *"for a square `Q` large enough and some `t₀ ∈ ℕ`"* (`b3_colle2.txt:597`).  The
square has to hold `r + 1` consecutive sites of the sweep line; since the window slides with
`t` along the very direction `d` the line runs in, one radius works for every `t`. -/

/-- A window radius large enough to contain `z₀ + j • d` for every `0 ≤ j ≤ r`. -/
def lineRadius (z₀ d : ℤ × ℤ) (r : ℕ) : ℕ :=
  (|z₀.1| + (r : ℤ) * |d.1| + |z₀.2| + (r : ℤ) * |d.2|).toNat

theorem lineRadius_cast (z₀ d : ℤ × ℤ) (r : ℕ) :
    ((lineRadius z₀ d r : ℕ) : ℤ) =
      |z₀.1| + (r : ℤ) * |d.1| + |z₀.2| + (r : ℤ) * |d.2| :=
  Int.toNat_of_nonneg (by positivity)

/-- The `r + 1` sites `z₀ + k • d`, `t ≤ k ≤ t + r`, all lie in the window of radius
`lineRadius z₀ d r` centred at `t • d`, uniformly in `t`. -/
theorem mem_winS_lineRadius (z₀ d : ℤ × ℤ) (r : ℕ) {t k : ℤ}
    (h0 : t ≤ k) (h1 : k ≤ t + (r : ℤ)) :
    z₀ + k • d ∈ winS (lineRadius z₀ d r) (t • d) := by
  have hi := lineRadius_cast z₀ d r
  have hd1 : (0 : ℤ) ≤ |d.1| := abs_nonneg _
  have hd2 : (0 : ℤ) ≤ |d.2| := abs_nonneg _
  have hz1 : (0 : ℤ) ≤ |z₀.1| := abs_nonneg _
  have hz2 : (0 : ℤ) ≤ |z₀.2| := abs_nonneg _
  have hrd1 : (0 : ℤ) ≤ (r : ℤ) * |d.1| := by positivity
  have hrd2 : (0 : ℤ) ≤ (r : ℤ) * |d.2| := by positivity
  have habs : ∀ x y : ℤ, |x + (k - t) * y| ≤ |x| + (r : ℤ) * |y| := by
    intro x y
    calc |x + (k - t) * y| ≤ |x| + |(k - t) * y| := abs_add_le _ _
      _ = |x| + |k - t| * |y| := by rw [abs_mul]
      _ ≤ |x| + (r : ℤ) * |y| := by
          have : |k - t| ≤ (r : ℤ) := by rw [abs_le]; omega
          gcongr
  have e1 : (z₀ + k • d).1 - (t • d).1 = z₀.1 + (k - t) * d.1 := by
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; ring
  have e2 : (z₀ + k • d).2 - (t • d).2 = z₀.2 + (k - t) * d.2 := by
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; ring
  have b1 := habs z₀.1 d.1
  have b2 := habs z₀.2 d.2
  rw [← e1] at b1
  rw [← e2] at b2
  rw [abs_le] at b1 b2
  rw [mem_winS, hi]
  refine ⟨⟨by linarith [b1.1], by linarith [b1.2]⟩, ⟨by linarith [b2.1], by linarith [b2.2]⟩⟩

/-- **`Nivat.Colle37.RegionLayers.gen`, reduced to the line structure of the top layer.**

The statement produced here is *literally* the `gen` field, with `v := d`.  What it consumes
is the layer split of `ShellLine.mem_shell_succ_iff` (`hsplit`, `hline`) together with the
`S_φ`-side data of `genClosure_ray`.  The window radius and the threshold on `t` are
constructed, not assumed: `i := lineRadius z₀ d r` and `M := L.toNat`.

This is the whole of Collé's closing sentence at `b3_colle2.txt:597` once the geometry
(`hdown`, `hup`) is granted. -/
theorem gen_of_line {A : ℕ → Set (ℤ × ℤ)} {ε : ℕ} {S : Finset (ℤ × ℤ)}
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
          ∀ k : ℤ, L ≤ k → z₀ + k • d + (b - a') ∈ A ε) :
    ∃ i M : ℕ, ∀ t : ℕ, M ≤ t → ∀ z ∈ A (ε + 1),
      GenClosure S (A ε ∪ (A (ε + 1) ∩ winS i ((t : ℤ) • d))) z := by
  refine ⟨lineRadius z₀ d r, L.toNat, ?_⟩
  intro t ht z hz
  have hLt : L ≤ (t : ℤ) := by omega
  rcases hsplit z hz with h | ⟨k, hkL, rfl⟩
  · exact GenClosure.base (Or.inl h)
  · refine genClosure_ray (M := (t : ℤ)) (r := r) hLt ha ha' hconv hconv' ?_ ?_ ?_ k hkL
    · intro b hb
      rcases hdown b hb with h | h
      · exact Or.inl h
      · exact Or.inr fun k hk => Or.inl (h k hk)
    · intro b hb
      rcases hup b hb with h | h
      · exact Or.inl h
      · exact Or.inr fun k hk => Or.inl (h k hk)
    · intro k h1 h2
      exact Or.inr ⟨hline k (le_trans hLt h1), mem_winS_lineRadius z₀ d r h1 h2⟩

end Nivat.Colle37
