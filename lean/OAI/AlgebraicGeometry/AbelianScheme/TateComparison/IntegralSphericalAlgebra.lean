import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SphericalBasis
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ConvolutionCoefficients
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IdentityCorrespondence

/-! # Integral Spherical Algebra -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralSphericalAlgebra

noncomputable section

/-! The rational span of the integral raw operators is a unital
subalgebra of the actual spherical Hecke algebra. -/

open scoped Classical

variable (s q : ℕ) [Fact q.Prime]

theorem sphericalBasis_identity : CentralConvolution.sphericalBasis s q (Local.IntegralType.identity s).val = 1 := by
  have h := CentralConvolution.sphericalBasis_central_shift s q (Local.IntegralType.identity s).val 1
  have he : (Local.IntegralType.identity s).val.shift 1 = Local.LocalType.central s := rfl
  rw [pow_one, he] at h
  exact (CentralConvolution.sphericalBasis_central_isUnit s q).mul_right_inj.mp (h.trans (mul_one _).symm)

def integralSphericalSpan : Submodule ℚ (HeckeKernel.Hecke s q) :=
  Submodule.span ℚ (Set.range (fun t : Local.IntegralType s => CentralConvolution.sphericalBasis s q t.val))

theorem integralSphericalSpan_basis (t : Local.IntegralType s) :
    CentralConvolution.sphericalBasis s q t.val ∈ integralSphericalSpan s q :=
  Submodule.subset_span ⟨t, rfl⟩

theorem integralSphericalSpan_one : (1 : HeckeKernel.Hecke s q) ∈ integralSphericalSpan s q := by
  rw [← sphericalBasis_identity s q]
  exact integralSphericalSpan_basis s q _

theorem integralSphericalSpan_mul (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (x y : HeckeKernel.Hecke s q)
    (hx : x ∈ integralSphericalSpan s q) (hy : y ∈ integralSphericalSpan s q) :
    x * y ∈ integralSphericalSpan s q := by
  apply LinearMap.BilinMap.apply_apply_mem_of_mem_span (integralSphericalSpan s q)
    (Set.range (fun t : Local.IntegralType s => CentralConvolution.sphericalBasis s q t.val))
    (Set.range (fun t : Local.IntegralType s => CentralConvolution.sphericalBasis s q t.val))
    (LinearMap.mul ℚ (HeckeKernel.Hecke s q)) ?_ x y hx hy
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
  change CentralConvolution.sphericalBasis s q u.val * CentralConvolution.sphericalBasis s q v.val ∈ _
  rw [ConvolutionCoefficients.spherical_convolution s q hElementaryDivisors]
  exact Submodule.sum_mem _ (fun w _ => nsmul_mem (integralSphericalSpan_basis s q w) _)

def integralSphericalAlgebra (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) : Subalgebra ℚ (HeckeKernel.Hecke s q) :=
  (integralSphericalSpan s q).toSubalgebra (integralSphericalSpan_one s q)
    (integralSphericalSpan_mul s q hElementaryDivisors)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralSphericalAlgebra
