import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Cast.Commute
import Mathlib.Tactic

/-! # Ring Integer Binomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RingIntegerBinomial

/-! The integer-coefficient binomial expansion inside any possibly noncommutative ring. -/

universe u

variable {R : Type u} [Ring R]

theorem ring_nsmul_pow (m i : ℕ) (x : R) : (m • x) ^ i = (m ^ i) • x ^ i := by
  simp only [nsmul_eq_mul]
  rw [(Nat.cast_commute m x).mul_pow, Nat.cast_pow]

theorem ringPower_integerBinomial (x : R) (m n : ℕ) :
    (1 + m • x) ^ n = ∑ i ∈ Finset.range (n + 1), (n.choose i * m ^ i) • x ^ i := by
  rw [add_comm (1 : R), (Commute.one_right (m • x)).add_pow]
  apply Finset.sum_congr rfl
  intro i _
  rw [one_pow, mul_one, ring_nsmul_pow]
  rw [← Nat.cast_comm (n.choose i) ((m ^ i) • x ^ i), ← nsmul_eq_mul, ← mul_smul]

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RingIntegerBinomial
