import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SphericalBasis
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ConvolutionCoefficients
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Commutativity

/-! # Coefficient Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CoefficientUniqueness

noncomputable section

/-! Raw kernel evaluation recovers the ordinary natural convolution
coefficients uniquely and proves their symmetry. -/

open scoped Classical

variable (s q : ℕ) [Fact q.Prime] (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])

include hElementaryDivisors in
theorem sphericalCoefficient_integral_sum (c : Local.IntegralType s →₀ ℕ) (w : Local.IntegralType s) :
    SphericalBasis.sphericalCoefficient s q w.val (c.sum (fun t n => n • CentralConvolution.sphericalBasis s q t.val)) = (c w : ℚ) := by
  rw [map_finsuppSum]
  have ht (t : Local.IntegralType s) (n : ℕ) :
      SphericalBasis.sphericalCoefficient s q w.val (n • CentralConvolution.sphericalBasis s q t.val) =
        if t = w then (n : ℚ) else 0 := by
    rw [map_nsmul, SphericalBasis.sphericalCoefficient_basis s q hElementaryDivisors]
    simp only [Subtype.val_inj, nsmul_eq_mul, mul_ite, mul_one, mul_zero]
  simp only [ht]
  simp_all

theorem convolutionCoefficients_unique (u v : Local.IntegralType s) (c : Local.IntegralType s →₀ ℕ)
    (hc : CentralConvolution.sphericalBasis s q u.val * CentralConvolution.sphericalBasis s q v.val =
      c.sum (fun t n => n • CentralConvolution.sphericalBasis s q t.val)) :
    c = ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors u v := by
  ext w
  have h := congrArg (SphericalBasis.sphericalCoefficient s q w.val)
    (hc.symm.trans (ConvolutionCoefficients.spherical_convolution s q hElementaryDivisors u v))
  rw [sphericalCoefficient_integral_sum s q hElementaryDivisors, sphericalCoefficient_integral_sum s q hElementaryDivisors] at h
  exact_mod_cast h

theorem convolutionCoefficients_comm (u v : Local.IntegralType s) :
    ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors u v = ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors v u := by
  apply convolutionCoefficients_unique s q hElementaryDivisors v u
  exact (Commutativity.spherical_mul_comm s q hElementaryDivisors _ _).trans (ConvolutionCoefficients.spherical_convolution s q hElementaryDivisors u v)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CoefficientUniqueness
