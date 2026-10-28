import OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDual
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactPointNormalization
import OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldCap

/-! # Canonical Local Dual Coordinates -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDualCoordinates.Constructions

noncomputable section

/-! The canonical point dual is the original normal class in translated complex coordinates. -/

open _root_.CategoryTheory OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldCap
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactPointNormalization.Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDual.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem canonicalLocalDual_zero (d : ℕ) :
    CanonicalLocalDual.Constructions.canonicalLocalDual d (0 : Fin d → ℂ) = Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass d := by
  symm
  apply CanonicalLocalDual.Constructions.canonicalLocalDual_unique
  rw [AlgebraicTopology.Duality.Poincare.ComplexManifoldCap.complexCanonicalLocalClass_eq_coordinate]
  have h := Geometric.ClosedBall.Cycles.complexCoordinatePointClass_to_origin d 0
  rw [HodgeConjecture.DegreeTwo.CompactPointNormalization.Constructions.localTranslationHomologyIso_zero, ModuleCat.id_apply] at h
  rw [h]
  exact AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison.complexNormalRationalDualClass_integralEvaluation d

theorem translationMapsTo (d : ℕ) (x : Fin d → ℂ) :
    Set.MapsTo (TopCat.isoOfHomeo (X := TopCat.of (Fin d → ℂ))
      (Y := TopCat.of (Fin d → ℂ)) (Homeomorph.subRight x)).hom ({x}ᶜ) ({0}ᶜ) := by
  intro y hy hz
  change y ≠ x at hy
  change y - x = 0 at hz
  exact hy (sub_eq_zero.mp hz)

theorem canonicalLocalDual_translation (d : ℕ) (x : Fin d → ℂ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (TopCat.isoOfHomeo (X := TopCat.of (Fin d → ℂ))
        (Y := TopCat.of (Fin d → ℂ)) (Homeomorph.subRight x)).hom
      (translationMapsTo d x) (2 * d) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass d) = CanonicalLocalDual.Constructions.canonicalLocalDual d x := by
  apply CanonicalLocalDual.Constructions.canonicalLocalDual_unique
  rw [AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation_naturality, AlgebraicTopology.Duality.Poincare.ComplexManifoldCap.complexCanonicalLocalClass_eq_coordinate]
  change AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of (Fin d → ℂ)) ({0}ᶜ) (2 * d)
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass d)
    ((Geometric.ClosedBall.Cycles.localTranslationHomologyIso (Fin d → ℂ) x (2 * d)).hom
      (Geometric.ClosedBall.Cycles.complexCoordinatePointClass d x)) = 1
  rw [Geometric.ClosedBall.Cycles.complexCoordinatePointClass_to_origin]
  exact AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison.complexNormalRationalDualClass_integralEvaluation d

end

end OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDualCoordinates.Constructions
