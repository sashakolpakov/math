import Mathlib

/-! # Nilpotence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Nilpotence

/-!
# IntegralComparison: nilpotence of divided-power thickenings

If p is nilpotent in a ring carrying divided powers, every element of
the divided-power ideal is nilpotent. The exponent is proved explicitly
from p^N = 0 and p^N dividing (N*p)!.
-/

lemma pow_dvd_mul_factorial (p N : ℕ) (hp : 0 < p) : p ^ N ∣ (N * p).factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ, Nat.succ_mul]
    exact (Nat.mul_dvd_mul ih (Nat.dvd_factorial hp le_rfl)).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

lemma nilpotent_of_mem {A : Type*} [CommRing A] {I : Ideal A}
    (δ : DividedPowers I) (p : ℕ) (hp : 0 < p) (hpn : IsNilpotent (p : A))
    {x : A} (hx : x ∈ I) : IsNilpotent x := by
  obtain ⟨N, hN⟩ := hpn
  obtain ⟨d, hd⟩ := pow_dvd_mul_factorial p N hp
  have hfac : ((N * p).factorial : A) = 0 := by
    rw [hd, Nat.cast_mul, Nat.cast_pow, hN, zero_mul]
  refine ⟨N * p, ?_⟩
  rw [← δ.factorial_mul_dpow_eq_pow hx, hfac, zero_mul]

end OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Nilpotence
