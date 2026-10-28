import OAI.AlgebraicGeometry.Comparison.Betti.Projective.ConcreteImage
import OAI.AlgebraicGeometry.Comparison.Betti.ReferenceDerivedNormalization

/-! # Concrete Derived -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.ConcreteDerived

noncomputable section

/-! The preserved algebraic-to-holomorphic cohomology map is an isomorphism for every smooth integral projective presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom] [IsSeparated X.hom]
  (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom)

include P in
theorem projectivePresentation_algebraicToHolomorphicCohomologyMap_isIso (n : ℕ) :
    IsIso (Holomorphic.Hypercohomology.algebraicToHolomorphicCohomologyMap X n) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have h := ConcreteImage.projectivePresentation_originalDirectImageCohomologyMap_bijective X P (n : ℤ)
  have he : (fun x => Holomorphic.Hypercohomology.algebraicToHolomorphicCohomologyMap X n x) =
      FlasqueDerived.directImageCohomologyMap (Analytification.Base.analytificationMap X) (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X)
        (Holomorphic.Int.analyticHolomorphicSheafComplexInt X) (Holomorphic.Int.algebraicToHolomorphicDirectImageInt X) (n : ℤ) :=
    funext (ReferenceDerivedNormalization.algebraicToHolomorphicCohomologyMap_eq_directImage X n)
  exact (congrArg Function.Bijective he).mpr h

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.ConcreteDerived
