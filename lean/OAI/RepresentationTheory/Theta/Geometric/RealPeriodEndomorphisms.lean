import OAI.RepresentationTheory.Theta.Geometric.RealPeriodHomology
import OAI.RepresentationTheory.Theta.Geometric.HomologyCommutingSquare

/-! # Real Period Endomorphisms -/

namespace OAI.RepresentationTheory.Theta.Geometric.RealPeriodEndomorphisms

noncomputable section

/-! Actual commutation on native points implies commutation of the
same real transport on original rational period endomorphisms. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.CategoryTheory.MonObj

namespace RealPeriodMaps

local instance realPeriodEndomorphisms_integral (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property

variable {A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (T : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →L[ℝ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B)
    (hT : ∀ v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A, T v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B)
    (f : AlgebraicGeometry.Betti.Scheme.schemePointSpace A.toOver ⟶ AlgebraicGeometry.Betti.Scheme.schemePointSpace B.toOver)
    (hf : ∀ v : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A,
      f (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input A (QuotientAddGroup.mk v)) =
        AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input B (QuotientAddGroup.mk (T v)))

include hf in
theorem rationalMap_endomorphism (a : A.toOver ⟶ A.toOver) (b : B.toOver ⟶ B.toOver)
    [IsMonHom a] [IsMonHom b]
    (h : f ≫ TopCat.ofHom (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous b) =
      TopCat.ofHom (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous a) ≫ f) (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift b (RealPeriodCoe.RealPeriodMaps.rationalMap T hT v) = RealPeriodCoe.RealPeriodMaps.rationalMap T hT (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift a v) := by
  apply (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods B).injective
  have hleft := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyNaturality.IntrinsicRationalPeriods.nativeHomologyPeriods_naturality b (RealPeriodCoe.RealPeriodMaps.rationalMap T hT v)
  have hright := RealPeriodHomology.RealPeriodMaps.nativeHomology_naturality T hT f hf (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift a v)
  have h₁ := congrArg (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ)
    (TopCat.ofHom (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous b)) 1) (RealPeriodHomology.RealPeriodMaps.nativeHomology_naturality T hT f hf v)
  have h₂ := congrArg (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f 1) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyNaturality.IntrinsicRationalPeriods.nativeHomologyPeriods_naturality a v)
  exact hleft.trans (h₁.trans ((HomologyCommutingSquare.homologyPushforward_commuting f
    (TopCat.ofHom (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous a))
    (TopCat.ofHom (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous b)) h 1 (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A v)).trans
      (h₂.symm.trans hright.symm)))

end RealPeriodMaps

end

end OAI.RepresentationTheory.Theta.Geometric.RealPeriodEndomorphisms
