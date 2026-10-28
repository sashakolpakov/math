import Mathlib.Data.Nat.Prime.Infinite

/-! # Auxiliary Prime Level -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.AuxiliaryPrimeLevel

section

/-! A prime auxiliary level can be chosen coprime to both the prescribed
level and the positive polarization degree. -/

theorem exists_auxiliary_prime_level (D N : ℕ) (hD : 0 < D) (hN : 0 < N) :
    ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ Nat.Coprime p D ∧ Nat.Coprime p N := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (max 3 (D * N + 1))
  have hprod : Nat.Coprime p (D * N) := hprime.coprime_iff_not_dvd.mpr (fun h => by
    have hle := Nat.le_of_dvd (Nat.mul_pos hD hN) h
    omega)
  exact ⟨p, hprime, (le_max_left _ _).trans hp,
    hprod.coprime_dvd_right (dvd_mul_right D N),
    hprod.coprime_dvd_right (dvd_mul_left N D)⟩

end

/-! The auxiliary prime can simultaneously avoid the prescribed level
and polarization degree and exceed any fixed embedding bound. -/

theorem exists_auxiliary_prime_level_above (D N B : ℕ) (hD : 0 < D) (hN : 0 < N) :
    ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ Nat.Coprime p D ∧ Nat.Coprime p N ∧ B < p := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (max 3 (max (D * N + 1) (B + 1)))
  have hprod : Nat.Coprime p (D * N) := hprime.coprime_iff_not_dvd.mpr (fun h => by
    have hle := Nat.le_of_dvd (Nat.mul_pos hD hN) h
    omega)
  exact ⟨p, hprime, (le_max_left _ _).trans hp,
    hprod.coprime_dvd_right (dvd_mul_right D N),
    hprod.coprime_dvd_right (dvd_mul_left N D), by omega⟩

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.AuxiliaryPrimeLevel
