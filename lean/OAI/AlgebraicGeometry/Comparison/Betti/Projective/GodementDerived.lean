import OAI.AlgebraicGeometry.Comparison.Betti.IntegerImageQuasiIso
import OAI.AlgebraicGeometry.Comparison.Betti.FlasqueDerived
import OAI.AlgebraicGeometry.Comparison.Betti.ReferenceGodement
import OAI.AlgebraicGeometry.Comparison.Betti.Godement.Hypercohomology

/-! # Godement Derived -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.GodementDerived

noncomputable section

/-! The original projective coefficient map gives a bijective normalized derived comparison on its canonical Godement resolutions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Comparison.Betti.Godement.Hypercohomology

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def originalHolomorphicGodementMapInt :=
  ImageExtensionSquare.extendDirectImageComplexMap (Analytification.Base.analytificationMap X)
    (Godement.PushforwardBicomplex.godementDirectImageTotalMap (Analytification.Base.analytificationMap X) (Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X))

theorem projectivePresentation_originalHolomorphicGodementMapInt_sections_quasiIso
    [IsSeparated X.hom] (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom) :
    QuasiIso (ImageAdjointNaturality.integerTopGlobalSectionsPullback (Analytification.Base.analytificationMap X) (originalHolomorphicGodementMapInt X)) :=
  IntegerImageQuasiIso.integerTopGlobalSectionsPullback_extend_quasiIso (Analytification.Base.analytificationMap X)
    (Godement.PushforwardBicomplex.godementDirectImageTotalMap (Analytification.Base.analytificationMap X) (Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X))
    (ReferenceGodement.projectivePresentation_originalHolomorphicGodementGlobalMap_quasiIso X P)

theorem projectivePresentation_godementDerivedComparison_bijective
    [IsSeparated X.hom] (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom) (n : ℤ) :
    Function.Bijective (FlasqueDerived.directImageCohomologyMap (Analytification.Base.analytificationMap X)
      (Godement.Hypercohomology.godementTotalComplexInt (X := TopCat.of X.left) (Algebraic.Sheaves.algebraicDeRhamSheafComplex X))
      (Godement.Hypercohomology.godementTotalComplexInt (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Algebraic.HolomorphicSheafMap.analyticHolomorphicSheafComplex X))
      (originalHolomorphicGodementMapInt X) n) := by
  have hAlg : (Godement.Hypercohomology.godementTotalComplexInt (X := TopCat.of X.left) (Algebraic.Sheaves.algebraicDeRhamSheafComplex X)).IsStrictlyGE 0 :=
    Godement.Hypercohomology.godementTotalComplexInt_nonnegative (X := TopCat.of X.left) (Algebraic.Sheaves.algebraicDeRhamSheafComplex X)
  have hHol : (Godement.Hypercohomology.godementTotalComplexInt (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Algebraic.HolomorphicSheafMap.analyticHolomorphicSheafComplex X)).IsStrictlyGE 0 :=
    Godement.Hypercohomology.godementTotalComplexInt_nonnegative (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (Algebraic.HolomorphicSheafMap.analyticHolomorphicSheafComplex X)
  exact @FlasqueDerived.directImageCohomologyMap_bijective_of_flasque (TopCat.of X.left)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Analytification.Base.analytificationMap X)
    (Godement.Hypercohomology.godementTotalComplexInt (X := TopCat.of X.left) (Algebraic.Sheaves.algebraicDeRhamSheafComplex X))
    (Godement.Hypercohomology.godementTotalComplexInt (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Algebraic.HolomorphicSheafMap.analyticHolomorphicSheafComplex X))
    (originalHolomorphicGodementMapInt X) n 0 0 hAlg hHol
    (FlasqueNatQuasiIso.extend_flasque (X := TopCat.of X.left) _ (Godement.TotalFlasque.godementTotal_isFlasque (X := TopCat.of X.left)
      (Algebraic.Sheaves.algebraicDeRhamSheafComplex X)))
    (FlasqueNatQuasiIso.extend_flasque (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) _ (Godement.TotalFlasque.godementTotal_isFlasque (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (Algebraic.HolomorphicSheafMap.analyticHolomorphicSheafComplex X)))
    (projectivePresentation_originalHolomorphicGodementMapInt_sections_quasiIso X P)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.GodementDerived
