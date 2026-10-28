import OAI.AlgebraicGeometry.Comparison.Betti.ReferenceGodementAugmentationInt
import OAI.AlgebraicGeometry.Comparison.Betti.DerivedQuasiIsoSquare
import OAI.AlgebraicGeometry.Comparison.Betti.ImageAdjointNaturality

/-! # Concrete Image -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.ConcreteImage

noncomputable section

/-! The original direct-image comparison is bijective on the preserved projective de Rham complexes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Comparison.Betti.ImageAdjointNaturality

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom] [IsSeparated X.hom]
  (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom)

include P in
theorem projectivePresentation_originalDirectImageCohomologyMap_bijective (n : ℤ) :
    Function.Bijective (FlasqueDerived.directImageCohomologyMap (Analytification.Base.analytificationMap X)
      (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X) (Holomorphic.Int.analyticHolomorphicSheafComplexInt X)
      (Holomorphic.Int.algebraicToHolomorphicDirectImageInt X) n) := by
  let f := Analytification.Base.analytificationMap X
  let F := TopologicalSheafPullback.sheafInverseImage f
  let α := Holomorphic.Int.algebraicToHolomorphicDirectImageInt X
  let γ := GodementDerived.originalHolomorphicGodementMapInt X
  let e := ReferenceGodementAugmentationInt.algebraicGodementAugmentationInt X
  let d := Godement.Hypercohomology.godementTotalAugmentationInt (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (Algebraic.HolomorphicSheafMap.analyticHolomorphicSheafComplex X)
  have hs := ImageAdjointNaturality.directImageAdjointComplexMap_square f α γ e d
    (ReferenceGodementAugmentationInt.originalHolomorphicGodementMapInt_augmentation X)
  exact DerivedQuasiIsoSquare.Ext.coefficientDerivedMap_bijective_of_quasiIso_square F
    (ConstantSheafSections.standardConstantSheaf (TopCat.of X.left)) (ConstantSheafSections.standardConstantSheaf (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
    (TopologicalSheafPullback.constantPullbackIso f).inv (ImageAdjointNaturality.directImageAdjointComplexMap f α) (ImageAdjointNaturality.directImageAdjointComplexMap f γ) e d hs
    (ReferenceGodementAugmentationInt.algebraicGodementAugmentationInt_quasiIso X)
    (Godement.Hypercohomology.godementTotalAugmentationInt_quasiIso (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (Algebraic.HolomorphicSheafMap.analyticHolomorphicSheafComplex X)) n
    (GodementDerived.projectivePresentation_godementDerivedComparison_bijective X P n)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.ConcreteImage
