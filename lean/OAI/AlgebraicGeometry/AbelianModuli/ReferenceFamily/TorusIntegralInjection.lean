import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularCoefficientLift
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularCoefficientInjection

/-! # Torus Integral Injection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorusIntegralInjection

noncomputable section

/-! The actual integral-to-rational coefficient map is injective in degree
two on a quotient of a real vector space by a discrete free lattice. -/

open _root_.CategoryTheory

abbrev RationalModuloIntegral := ℚ ⧸ (Int.castAddHom ℚ).range

def integralRationalCoefficient : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℚ :=
  ModuleCat.ofHom (Int.castAddHom ℚ).toIntLinearMap

def rationalModuloCoefficient : ModuleCat.of ℤ ℚ ⟶ ModuleCat.of ℤ RationalModuloIntegral :=
  ModuleCat.ofHom (QuotientAddGroup.mk' (Int.castAddHom ℚ).range).toIntLinearMap

theorem integralRationalCoefficient_injective : Function.Injective integralRationalCoefficient :=
  Int.cast_injective

theorem rationalModuloCoefficient_surjective : Function.Surjective rationalModuloCoefficient :=
  QuotientAddGroup.mk_surjective

theorem integralRationalModulo_exact (b : ℚ) :
    rationalModuloCoefficient b = 0 ↔ ∃ a : ℤ, integralRationalCoefficient a = b :=
  QuotientAddGroup.eq_zero_iff b

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (Λ : Submodule ℤ V) [DiscreteTopology Λ] [Module.Free ℤ Λ]

theorem torus_integralH2_rational_injective :
    Function.Injective (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap integralRationalCoefficient (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 2) :=
  SingularCoefficientInjection.singularH2_coefficient_injective integralRationalCoefficient rationalModuloCoefficient
    (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) integralRationalCoefficient_injective rationalModuloCoefficient_surjective
    integralRationalModulo_exact
    (SingularCoefficientLift.singularH1_coefficient_surjective rationalModuloCoefficient rationalModuloCoefficient_surjective Λ)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorusIntegralInjection
