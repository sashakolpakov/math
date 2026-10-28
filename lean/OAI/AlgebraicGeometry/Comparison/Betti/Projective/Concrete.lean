import OAI.AlgebraicGeometry.Comparison.Betti.Projective.ConcreteDerived
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DeRham

/-! # Concrete -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.Concrete

noncomputable section

/-! The original algebraic de Rham–Betti map is an isomorphism in every degree for smooth integral projective presentations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom] [IsSeparated X.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom)

include P in
theorem projectivePresentation_algebraicDeRhamBettiMap_isIso (n : ℕ) :
    IsIso (Algebraic.Map.algebraicDeRhamBettiMap X n) := by
  have h : IsIso (Holomorphic.Hypercohomology.algebraicToHolomorphicCohomologyMap X n) :=
    ConcreteDerived.projectivePresentation_algebraicToHolomorphicCohomologyMap_isIso X P n
  rw [← Holomorphic.DeRham.algebraicDeRhamBettiMap_holomorphic_factorization X n]
  infer_instance

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.Concrete
