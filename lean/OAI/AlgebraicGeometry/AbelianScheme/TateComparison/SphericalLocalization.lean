import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralSphericalAlgebra
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SubalgebraLocalization
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Commutativity

/-! # Spherical Localization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SphericalLocalization

noncomputable section

/-! The full actual spherical Hecke algebra is the localization of its
integral subalgebra at the raw central operator. -/

variable (s q : ℕ) [Fact q.Prime] (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])

abbrev sphericalCommRing : CommRing (HeckeKernel.Hecke s q) where
  toRing := inferInstance
  mul_comm := Commutativity.spherical_mul_comm s q hElementaryDivisors

def integralCentralElement : IntegralSphericalAlgebra.integralSphericalAlgebra s q hElementaryDivisors :=
  ⟨CentralConvolution.sphericalBasis s q (Local.LocalType.central s), IntegralSphericalAlgebra.integralSphericalSpan_basis s q (Local.IntegralType.central s)⟩

theorem spherical_denominator_clearing (x : HeckeKernel.Hecke s q) :
    ∃ n : ℕ, CentralConvolution.sphericalBasis s q (Local.LocalType.central s) ^ n * x ∈ IntegralSphericalAlgebra.integralSphericalAlgebra s q hElementaryDivisors := by
  let := sphericalCommRing s q hElementaryDivisors
  apply SpanDenominatorClearing.centralPower_clear_span (IntegralSphericalAlgebra.integralSphericalAlgebra s q hElementaryDivisors) (integralCentralElement s q hElementaryDivisors)
    (CentralConvolution.sphericalBasis s q) (RationalSpan.sphericalBasis_span s q hElementaryDivisors) ?_ x
  intro t
  obtain ⟨n, u, hu⟩ := CentralConvolution.sphericalBasis_exists_integral_shift s q t
  refine ⟨n, ?_⟩
  change CentralConvolution.sphericalBasis s q (Local.LocalType.central s) ^ n * CentralConvolution.sphericalBasis s q t ∈ IntegralSphericalAlgebra.integralSphericalAlgebra s q hElementaryDivisors
  rw [hu]
  exact IntegralSphericalAlgebra.integralSphericalSpan_basis s q u

theorem spherical_isLocalization :
    let := sphericalCommRing s q hElementaryDivisors
    IsLocalization.Away (integralCentralElement s q hElementaryDivisors) (HeckeKernel.Hecke s q) := by
  let := sphericalCommRing s q hElementaryDivisors
  exact SubalgebraLocalization.subalgebra_awayLocalization (IntegralSphericalAlgebra.integralSphericalAlgebra s q hElementaryDivisors)
    (integralCentralElement s q hElementaryDivisors) (CentralConvolution.sphericalBasis_central_isUnit s q)
    (spherical_denominator_clearing s q hElementaryDivisors)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SphericalLocalization
