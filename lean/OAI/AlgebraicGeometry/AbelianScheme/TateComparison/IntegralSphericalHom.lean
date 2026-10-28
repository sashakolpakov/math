import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralSphericalAlgebra
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LinearMultiplicativity

/-! # Integral Spherical Hom -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralSphericalHom

noncomputable section

/-! An actual family satisfying integral convolution defines an algebra
homomorphism on the integral spherical subalgebra. -/

open scoped Classical

variable (s q : ℕ) [Fact q.Prime] (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
  {A : Type*} [Ring A] [Algebra ℚ A] (a : Local.IntegralType s → A)

def integralSphericalLinear : HeckeKernel.Hecke s q →ₗ[ℚ] A :=
  (SphericalBasis.sphericalModuleBasis s q hElementaryDivisors).constr ℚ
    (fun t => if h : t.IsIntegral then a ⟨t, h⟩ else 0)

theorem integralSphericalLinear_basis (t : Local.IntegralType s) :
    integralSphericalLinear s q hElementaryDivisors a (CentralConvolution.sphericalBasis s q t.val) = a t := by
  rw [← SphericalBasis.sphericalModuleBasis_apply s q hElementaryDivisors]
  simp only [integralSphericalLinear, Module.Basis.constr_basis, dite_eq_left t.property]

def integralSphericalHom
    (h1 : a (Local.IntegralType.identity s) = 1)
    (hmul : ∀ u v, a u * a v = (ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors u v).sum (fun w n => n • a w)) :
    IntegralSphericalAlgebra.integralSphericalAlgebra s q hElementaryDivisors →ₐ[ℚ] A := by
  let f := integralSphericalLinear s q hElementaryDivisors a
  apply AlgHom.ofLinearMap (f.comp (IntegralSphericalAlgebra.integralSphericalAlgebra s q hElementaryDivisors).val.toLinearMap)
  · change f 1 = 1
    rw [← IntegralSphericalAlgebra.sphericalBasis_identity s q]
    exact (integralSphericalLinear_basis s q hElementaryDivisors a _).trans h1
  · intro x y
    change f (x.val * y.val) = f x.val * f y.val
    apply LinearMultiplicativity.linearMap_mul_on_span (fun t : Local.IntegralType s => CentralConvolution.sphericalBasis s q t.val) f ?_ x.property y.property
    intro u v
    simp only [f, integralSphericalLinear_basis, ConvolutionCoefficients.spherical_convolution s q hElementaryDivisors,
      map_finsuppSum, map_nsmul]
    exact (hmul u v).symm

theorem integralSphericalHom_basis
    (h1 : a (Local.IntegralType.identity s) = 1)
    (hmul : ∀ u v, a u * a v = (ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors u v).sum (fun w n => n • a w))
    (t : Local.IntegralType s) :
    integralSphericalHom s q hElementaryDivisors a h1 hmul
      ⟨CentralConvolution.sphericalBasis s q t.val, IntegralSphericalAlgebra.integralSphericalSpan_basis s q t⟩ = a t :=
  integralSphericalLinear_basis s q hElementaryDivisors a t

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralSphericalHom
