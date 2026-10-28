import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.Hypercohomology
import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Map

/-! # De Rham -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DeRham

noncomputable section

/-! The actual BettiComparison map factors through holomorphic hypercohomology and a proved Betti isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]

def holomorphicBettiCohomologyIso (n : ℕ) : Hypercohomology.analyticHolomorphicCohomology X n ≅ Algebraic.Sheaves.betti X n :=
  Hypercohomology.holomorphicConstantCohomologyIso X n ≪≫ Algebraic.Map.analyticConstantBettiIso X n

theorem algebraicDeRhamBettiMap_holomorphic_factorization (n : ℕ) :
    Hypercohomology.algebraicToHolomorphicCohomologyMap X n ≫ (holomorphicBettiCohomologyIso X n).hom =
      Algebraic.Map.algebraicDeRhamBettiMap X n := by
  change Hypercohomology.algebraicToHolomorphicCohomologyMap X n ≫
    ((Hypercohomology.holomorphicConstantCohomologyIso X n).hom ≫ (Algebraic.Map.analyticConstantBettiIso X n).hom) = _
  rw [← Category.assoc, Hypercohomology.algebraicToHolomorphicCohomologyMap_factorization]
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DeRham
