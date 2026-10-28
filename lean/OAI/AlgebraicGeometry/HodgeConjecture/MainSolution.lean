import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GeometricAlgebraicity
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.IntrinsicCycleSpan
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ComponentComparison

/-! # Main Solution -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.MainSolution

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

/-!
# Solution to the Hodge conjecture for CM abelian varieties

The conclusion is the literal conclusion of the upstream abelian-variety
special case. The only added condition is complex multiplication on H¹.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint

/-- Every rational Hodge class on a complex CM abelian variety is a rational
linear combination of classes of algebraic subvarieties. -/
theorem hodge_conjecture_for_cm_abelian_varieties
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [Foundations.ProjectiveSpaceIs.IsProjective X.hom] [GrpObj X]
    (hCM : ComplexMultiplication.Definitions.HasComplexMultiplication X) (p : ℕ) :
    Hdg^p(X; ℚ) ≤ ComplexPoint.Basic.ComplexSchemePoint.algebraicCycleClassSpan X p := by
  intro a ha
  obtain ⟨z, hz⟩ := ComplexMultiplication.Reference.GeometricAlgebraicity.originalHodgeClass_nativeThomAlgebraic X hCM p a ha
  have hm := ComplexMultiplication.Reference.IntrinsicCycleSpan.originalNativeCycle_mem_span X p
    (fun x => ComplexMultiplication.Reference.ComponentComparison.originalComponentClass_comparison X p x) z
  rw [hz, (ComplexMultiplication.Reference.EvenHodgeClasses.originalEvenBettiBridge X p).apply_symm_apply a] at hm
  exact hm

end OAI.AlgebraicGeometry.HodgeConjecture.MainSolution
