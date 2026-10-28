import OAI.AlgebraicGeometry.Comparison.Betti.Projective.GodementDerived
import OAI.AlgebraicGeometry.Comparison.Betti.ImageExtensionSquare

/-! # Reference Godement Augmentation Int -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ReferenceGodementAugmentationInt

noncomputable section

/-! The original integer algebraic source and coefficient map retain the Godement augmentation square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Comparison.Betti.ImageExtensionSquare

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def algebraicGodementAugmentationInt : Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X ⟶
    Godement.Hypercohomology.godementTotalComplexInt (X := TopCat.of X.left) (Algebraic.Sheaves.algebraicDeRhamSheafComplex X) :=
  (Analytic.De.algebraicSheafIntExtensionIso X).hom ≫
    Godement.Hypercohomology.godementTotalAugmentationInt (X := TopCat.of X.left) (Algebraic.Sheaves.algebraicDeRhamSheafComplex X)

omit [IsIntegral X.left] [Smooth X.hom] in
theorem algebraicGodementAugmentationInt_quasiIso : QuasiIso (algebraicGodementAugmentationInt X) :=
  quasiIso_comp _ _ (hφ := quasiIso_of_isIso (Analytic.De.algebraicSheafIntExtensionIso X).hom)
    (hφ' := Godement.Hypercohomology.godementTotalAugmentationInt_quasiIso (X := TopCat.of X.left) (Algebraic.Sheaves.algebraicDeRhamSheafComplex X))

theorem originalHolomorphicGodementMapInt_augmentation :
    algebraicGodementAugmentationInt X ≫ Projective.GodementDerived.originalHolomorphicGodementMapInt X =
      Holomorphic.Int.algebraicToHolomorphicDirectImageInt X ≫
        ((TopologicalSheafPullback.sheafDirectImage (Analytification.Base.analytificationMap X)).mapHomologicalComplex (.up ℤ)).map
          (Godement.Hypercohomology.godementTotalAugmentationInt (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
            (Algebraic.HolomorphicSheafMap.analyticHolomorphicSheafComplex X)) := by
  have hn := ImageExtensionSquare.extendDirectImageComplexMap_square (Analytification.Base.analytificationMap X)
    (Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X)
    (Godement.PushforwardBicomplex.godementDirectImageTotalMap (Analytification.Base.analytificationMap X) (Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X))
    (Godement.Bicomplex.godementTotalAugmentation (X := TopCat.of X.left) (Algebraic.Sheaves.algebraicDeRhamSheafComplex X))
    (Godement.Bicomplex.godementTotalAugmentation (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Algebraic.HolomorphicSheafMap.analyticHolomorphicSheafComplex X))
    (Godement.PushforwardBicomplex.godementDirectImageTotalMap_augmentation (Analytification.Base.analytificationMap X) (Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X))
  exact (Category.assoc _ _ _).trans
    ((congrArg ((Analytic.De.algebraicSheafIntExtensionIso X).hom ≫ ·) hn).trans (Category.assoc _ _ _).symm)

end

end OAI.AlgebraicGeometry.Comparison.Betti.ReferenceGodementAugmentationInt
