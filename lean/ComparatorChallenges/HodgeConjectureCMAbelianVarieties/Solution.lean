import OAI.AlgebraicGeometry.HodgeConjecture.MainSubmission

/-! # The CM Hodge conjecture -/

namespace HodgeCM

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint
open CategoryTheory AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoint

/-- Rational Hodge classes on a CM abelian variety are algebraic. -/
theorem hodge_conjecture_for_cm_abelian_varieties
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs.IsProjective X.hom] [GrpObj X]
    (hCM : OAI.AlgebraicGeometry.ComplexMultiplication.Definitions.HasComplexMultiplication X) (p : ℕ) :
    Hdg^p(X; ℚ) ≤ OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.algebraicCycleClassSpan X p :=
  OAI.AlgebraicGeometry.HodgeConjecture.MainSolution.hodge_conjecture_for_cm_abelian_varieties X hCM p

end HodgeCM
