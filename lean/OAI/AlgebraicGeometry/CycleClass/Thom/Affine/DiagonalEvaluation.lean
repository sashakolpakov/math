import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.CoordinateSectionMaps
import OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticCoordinateDifference
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PointProduct

/-! # Diagonal Evaluation -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalEvaluation.Constructions

noncomputable section

/-! Evaluating the actual diagonal sections is precisely the difference
of the actual coordinate vectors on the two original product factors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped MonoidalCategory TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.CoordinateSectionMaps.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalEquations.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleSectionVector.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Section.VectorHeadChange.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticCoordinateDifference.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PointProduct.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] (n : ℕ)
  [Algebra (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
  [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]

def diagonalVector : TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X ⊗ X)) ⟶ TopCat.of (Fin n → ℂ) :=
  Section.VectorHeadChange.Constructions.sectionVectorEquation (X ⊗ X) n (DiagonalEquations.Constructions.coordinateDifferenceSection X n)

theorem diagonalVector_eq_difference :
    (diagonalVector X n : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X ⊗ X) → (Fin n → ℂ)) =
      AnalyticCoordinateDifference.Constructions.coordinateDifference n (Section.VectorHeadChange.Constructions.sectionVectorEquation X n (EtaleSectionVector.Constructions.coordinateSections X n)) ∘ Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X := by
  funext z i
  change DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation z (DiagonalEquations.Constructions.coordinateDifferenceSection X n i) =
    DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (fst X X) z) (EtaleSectionVector.Constructions.coordinateSections X n i) -
      DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (snd X X) z) (EtaleSectionVector.Constructions.coordinateSections X n i)
  rw [CoordinateSectionMaps.Constructions.coordinateDifferenceSection_eq, map_sub]
  rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalEvaluation.Constructions
