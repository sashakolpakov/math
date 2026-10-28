import OAI.RepresentationTheory.Theta.Geometric.RealPeriodCoe
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection

/-! # Real Period Linear Ext -/

namespace OAI.RepresentationTheory.Theta.Geometric.RealPeriodLinearExt.RealPeriodMaps

noncomputable section

/-! Original rational periods determine a real-linear map on the
entire tangent space, because their integral lattice spans over R. -/

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods

variable {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem realLinear_ext_of_rational (T S : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℝ] W)
    (h : ∀ v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A, T v.val = S v.val) : T = S := by
  apply (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A).ext
  intro i
  rw [AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.realPeriodBasis_eq_rational]
  exact h (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A i)

theorem realContinuousLinear_ext_of_rational (T S : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →L[ℝ] W)
    (h : ∀ v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A, T v.val = S v.val) : T = S := by
  apply ContinuousLinearMap.ext
  intro v
  exact LinearMap.congr_fun (realLinear_ext_of_rational T.toLinearMap S.toLinearMap h) v

end

end OAI.RepresentationTheory.Theta.Geometric.RealPeriodLinearExt.RealPeriodMaps
