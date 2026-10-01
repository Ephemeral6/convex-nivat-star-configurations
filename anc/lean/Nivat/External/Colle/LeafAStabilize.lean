import Nivat.Defs.Config
import Nivat.External.Colle.ChainMax

set_option autoImplicit false

namespace Nivat

open Nivat.Colle35

/-- If `h • vl` is a period of `f` and `a ≡ b [MOD h]`, then translating `f` by `a•vl` and by
`b•vl` give the same configuration.  The periodicity link needed to reconcile a common
pigeonholed exponent `k` (known only mod the period length `h`) with the private per-index
exponents `k_i`. -/
theorem T_smul_eq_of_mod_eq {α : Type*} {f : Config α} {vl : ℤ × ℤ} {h : ℕ}
    (hper : (h : ℤ) • vl ∈ Per f) {a b : ℕ} (hab : a % h = b % h) :
    T ((a : ℤ) • vl) f = T ((b : ℤ) • vl) f := by
  have hmod : (a : ℤ) % (h : ℤ) = (b : ℤ) % (h : ℤ) := by
    have := congrArg (fun n : ℕ => (n : ℤ)) hab
    simpa [Int.natCast_mod] using this
  have hdvd : (h : ℤ) ∣ (b : ℤ) - (a : ℤ) := Int.ModEq.dvd hmod
  obtain ⟨c, hc⟩ := hdvd
  set diff : ℤ × ℤ := (b : ℤ) • vl - (a : ℤ) • vl with hdiff
  have hsmul : diff = c • ((h : ℤ) • vl) := by
    rw [hdiff, show (b:ℤ) • vl - (a:ℤ) • vl = ((b:ℤ) - (a:ℤ)) • vl by rw [sub_smul], hc, mul_smul]
    exact smul_comm (h:ℤ) c vl
  have hperc : diff ∈ Per f := hsmul ▸ (Per f).zsmul_mem hper c
  have hT' : ∀ w, f (w + diff) = f w := fun w => congrFun hperc w
  funext z
  have hz := hT' (z + (a : ℤ) • vl)
  have heq : z + (a : ℤ) • vl + diff = z + (b : ℤ) • vl := by
    rw [hdiff]; abel
  rw [heq] at hz
  simpa [T_apply] using hz.symm

/-- **Exact stabilization along a common exponent `k`.**  Given `A_i ⊆ A_j` (`:486`,
`hmono`) and the agreement fact `agreeA_of_max` (`ChainMax.lean:101`), the translates
`ϑ_i := T (k•vl + u i) η` agree with each other, not just with `xper`, on `hatOf A (const k) vl i`
for `i ≤ j`.  This is `b3_colle2.txt`'s "`ϑ_{i'}|_{Â_i} = ϑ_i|_{Â_i}` for all `i ≤ i'`" once `Â_i`
is read with the pigeonholed common `k` in place of the private `k_i`. -/
theorem stabilize_of_mono_agree {α : Type*} {η xper : Config α} {vl : ℤ × ℤ}
    {A : ℕ → Set (ℤ × ℤ)} {u : ℕ → ℤ × ℤ} (k : ℕ)
    (hmono : ∀ i j, i ≤ j → A i ⊆ A j)
    (hagree : ∀ i, ∀ z ∈ A i, η (z + u i) = xper z) :
    ∀ i j, i ≤ j → ∀ z ∈ hatOf A (fun _ => k) vl i,
      T ((k : ℤ) • vl + u i) η z = T ((k : ℤ) • vl + u j) η z := by
  intro i j hij z hz
  have hzj : z ∈ hatOf A (fun _ => k) vl j := hmono i j hij hz
  have hz' : z + (k : ℤ) • vl ∈ A i := hz
  have hzj' : z + (k : ℤ) • vl ∈ A j := hzj
  have hi := hagree i _ hz'
  have hj := hagree j _ hzj'
  show η (z + ((k : ℤ) • vl + u i)) = η (z + ((k : ℤ) • vl + u j))
  rw [show z + ((k:ℤ) • vl + u i) = (z + (k:ℤ) • vl) + u i by abel,
      show z + ((k:ℤ) • vl + u j) = (z + (k:ℤ) • vl) + u j by abel, hi, hj]

end Nivat
