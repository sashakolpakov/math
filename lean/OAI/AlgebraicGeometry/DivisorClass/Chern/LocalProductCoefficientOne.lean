import OAI.AlgebraicGeometry.DivisorClass.Chern.ZeroTangentCrossCycle
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ProductCupNormalization

/-! # Local Product Coefficient One -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.LocalProductCoefficientOne

noncomputable section

/-!
# ChernClass: the original local normal-line cup coefficient is one

The zero-dimensional tangent case uses the original projected point
generator and the proved right-point cross homotopy. Together with the
explicit positive-dimensional disk product, this covers every dimension.
-/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem zeroTangentCoordinateDual_evaluation :
    CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of ((Fin 1 → ℂ) × (Fin 0 → ℂ))) ({0}ᶜ) 2
      (CycleClass.Geometric.ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass ZeroTangentCrossCycle.zeroTangentComplexCoordinates) (HodgeConjecture.DegreeTwo.LocalProductGenerator.Constructions.localProductCrossGenerator 1 0) = 1 := by
  change CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ)
    (TopCat.of ((Fin 1 → ℂ) × (Fin 0 → ℂ))) ({0}ᶜ) 2
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (TopCat.prodFst (X := TopCat.of (Fin 1 → ℂ)) (Y := TopCat.of (Fin 0 → ℂ)))
      ZeroTangentCrossCycle.zeroTangentProjection_puncture 2 (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)) (HodgeConjecture.DegreeTwo.LocalProductGenerator.Constructions.localProductCrossGenerator 1 0) = 1
  rw [CycleClass.Geometric.RelativeUniversalCoefficientNaturality.Cycles.relativeHomologyEvaluation_naturality, ZeroTangentCrossCycle.zeroTangentCrossGenerator_projection]
  exact CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass_evaluation 1

theorem localProductCupCoefficient_line_zero : HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.localProductCupCoefficient 1 0 = 1 := by
  have h := HodgeConjecture.DegreeTwo.LocalProductCup.Constructions.localProductCupClass_evaluation 1 0
  change CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ)
    (TopCat.of ((Fin 1 → ℂ) × (Fin 0 → ℂ))) ({0}ᶜ) 2
    (HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.localProductCupTop 1 0) (HodgeConjecture.DegreeTwo.LocalProductGenerator.Constructions.localProductCrossGenerator 1 0) = 1 at h
  rw [HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.localProductCupTop_eq_smul_coordinates 1 0 ZeroTangentCrossCycle.zeroTangentComplexCoordinates, map_smul] at h
  change HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.localProductCupCoefficient 1 0 *
    CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Fin 1 → ℂ) × (Fin 0 → ℂ))) ({0}ᶜ) 2
      (CycleClass.Geometric.ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass ZeroTangentCrossCycle.zeroTangentComplexCoordinates) (HodgeConjecture.DegreeTwo.LocalProductGenerator.Constructions.localProductCrossGenerator 1 0) = 1 at h
  rw [zeroTangentCoordinateDual_evaluation, mul_one] at h
  exact h

theorem localProductCupCoefficient_line (d : ℕ) : HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.localProductCupCoefficient 1 d = 1 := by
  cases d with
  | zero => exact localProductCupCoefficient_line_zero
  | succ p => exact Line.ProductCupNormalization.localProductCupCoefficient_line_positive p

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.LocalProductCoefficientOne
