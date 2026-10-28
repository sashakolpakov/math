import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Data.Nat.Choose.Cast

noncomputable section
open _root_.MeasureTheory
open scoped Nat

namespace OAI.LinearAlgebra.Moore

/-- The ordinary real beta integral at nonnegative integer exponents. -/
theorem integral_pow_mul_one_sub_pow (a b : ℕ) :
    (∫ t in (0:ℝ)..1, t^a*(1-t)^b) =
      (a.factorial:ℝ)*b.factorial/(a+b+1).factorial := by
  have he := Complex.betaIntegral_eq_Gamma_mul_div ((a:ℂ)+1) ((b:ℂ)+1)
    (by simp only [Complex.add_re,Complex.natCast_re,Complex.one_re]; positivity)
    (by simp only [Complex.add_re,Complex.natCast_re,Complex.one_re]; positivity)
  have hsum : ((a:ℂ)+1)+((b:ℂ)+1) = ((a+b+1:ℕ):ℂ)+1 := by
    push_cast
    ring
  rw [hsum,Complex.Gamma_nat_eq_factorial,Complex.Gamma_nat_eq_factorial,
    Complex.Gamma_nat_eq_factorial] at he
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  push_cast
  simpa only [Complex.betaIntegral,add_sub_cancel_right,Complex.cpow_natCast] using he

/-- Every Bernstein basis polynomial of degree `m` has the same integral
`1/(m+1)`, including the two endpoint exponents. -/
theorem bernstein_integral (m j : ℕ) (hj : j ≤ m) :
    (m.choose j:ℝ)*(∫ t in (0:ℝ)..1, t^(m-j)*(1-t)^j) = 1/((m:ℝ)+1) := by
  rw [integral_pow_mul_one_sub_pow]
  have hind : m-j+j+1 = m+1 := by omega
  rw [hind]
  simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  have hfactor : (m.choose j:ℝ)*(j.factorial:ℝ)*(m-j).factorial = m.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
  have hfac : (m.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  calc
    _ = ((m.choose j:ℝ)*j.factorial*(m-j).factorial)/(((m:ℝ)+1)*m.factorial) := by ring
    _ = (m.factorial:ℝ)/(((m:ℝ)+1)*m.factorial) := by rw [hfactor]
    _ = _ := by field_simp

theorem intervalIntegrable_bernstein (m j : ℕ) :
    IntervalIntegrable (fun t : ℝ => t^(m-j)*(1-t)^j) volume 0 1 := by
  exact ((continuous_id.pow _).mul ((continuous_const.sub continuous_id).pow _)).intervalIntegrable _ _

end OAI.LinearAlgebra.Moore
