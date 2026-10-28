import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Tactic

/-! # Prime Binomial Divisibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrimeBinomialDivisibility

/-! Higher binomial coefficients acquire an extra prime factor after substitution by a sufficiently deep prime power. -/

theorem primeBinomial_highTerm_divisible (q r i : ℕ) (hq : q.Prime) (hr : 0 < r)
    (hi : 2 ≤ i) (hiq : i ≤ q) (hsize : r + 2 ≤ r * q) :
    q ^ (r + 2) ∣ q.choose i * (q ^ r) ^ i := by
  rw [← pow_mul]
  by_cases he : i = q
  · subst i
    rw [Nat.choose_self, one_mul]
    exact pow_dvd_pow q hsize
  · have hiq' : i < q := lt_of_le_of_ne hiq he
    obtain ⟨c, hc⟩ := hq.dvd_choose_self (by omega) hiq'
    have hri : r * 2 ≤ r * i := Nat.mul_le_mul_left r hi
    have hexp : r + 2 ≤ r * i + 1 := by omega
    apply dvd_trans (pow_dvd_pow q hexp)
    refine ⟨c, ?_⟩
    rw [hc, pow_succ]
    ac_rfl

theorem primeBinomial_highTerm_divisible_of_odd (q r i : ℕ) (hq : q.Prime) (hodd : 3 ≤ q)
    (hr : 0 < r) (hi : 2 ≤ i) (hiq : i ≤ q) :
    q ^ (r + 2) ∣ q.choose i * (q ^ r) ^ i := by
  have hmul : r * 3 ≤ r * q := Nat.mul_le_mul_left r hodd
  exact primeBinomial_highTerm_divisible q r i hq hr hi hiq (by omega)

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrimeBinomialDivisibility
