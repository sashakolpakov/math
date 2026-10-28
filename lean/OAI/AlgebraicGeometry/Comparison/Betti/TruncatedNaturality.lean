import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.FiltrationExtension
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.Truncated
import OAI.AlgebraicGeometry.Comparison.Betti.ReferenceDerivedNormalization
import OAI.AlgebraicGeometry.Comparison.Betti.CoefficientDerivedNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.ImageAdjointNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.ImageExtensionSquare

/-! # Truncated Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.TruncatedNaturality

noncomputable section

/-! The actual algebraic-to-holomorphic map intertwines the independent truncation inclusions on the preserved integer complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def holomorphicTruncationComplexInt (r : ℤ) : CochainComplex (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) ℤ :=
  (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (Algebraic.HolomorphicSheafMap.analyticHolomorphicSheafComplex X) r).extend (ComplexShape.embeddingUpIntGE 0)

def holomorphicTruncationInclusionInt (r : ℤ) : holomorphicTruncationComplexInt X r ⟶
    Holomorphic.Int.analyticHolomorphicSheafComplexInt X :=
  HomologicalComplex.extendMap (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (Algebraic.HolomorphicSheafMap.analyticHolomorphicSheafComplex X) r) (ComplexShape.embeddingUpIntGE 0)

abbrev holomorphicTruncatedCohomology (n : ℕ) (r : ℤ) :=
  (DerivedCategory.singleFunctor (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) 0).obj (Analytic.De.analyticConstantSheaf X) ⟶
    (DerivedCategory.Q.obj (holomorphicTruncationComplexInt X r))⟦(n : ℤ)⟧

def holomorphicTruncationClass (n : ℕ) (r : ℤ) :
    holomorphicTruncatedCohomology X n r →ₗ[ℂ] Holomorphic.Hypercohomology.analyticHolomorphicCohomology X n :=
  Linear.rightComp ℂ _ ((DerivedCategory.Q.map (holomorphicTruncationInclusionInt X r))⟦(n : ℤ)⟧')

def algebraicHolomorphicTruncatedDirectImageInt (r : ℤ) :=
  ImageExtensionSquare.extendDirectImageComplexMap (Analytification.Base.analytificationMap X)
    (BrutalCechAcyclicity.Hodge.brutalSheafDirectImageMap (Analytification.Base.analytificationMap X) (Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X) r)

theorem algebraicHolomorphicTruncation_square (r : ℤ) :
    Algebraic.FiltrationExtension.algebraicTruncationInclusionInt X r ≫ Holomorphic.Int.algebraicToHolomorphicDirectImageInt X =
      algebraicHolomorphicTruncatedDirectImageInt X r ≫
        ((TopologicalSheafPullback.sheafDirectImage (Analytification.Base.analytificationMap X)).mapHomologicalComplex (.up ℤ)).map
          (holomorphicTruncationInclusionInt X r) := by
  let i := HomologicalComplex.extendMap (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (Algebraic.Sheaves.algebraicDeRhamSheafComplex X) r)
    (ComplexShape.embeddingUpIntGE 0)
  have hn := ImageExtensionSquare.extendDirectImageComplexMap_square (Analytification.Base.analytificationMap X)
    (BrutalCechAcyclicity.Hodge.brutalSheafDirectImageMap (Analytification.Base.analytificationMap X) (Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X) r)
    (Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X) (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (Algebraic.Sheaves.algebraicDeRhamSheafComplex X) r)
    (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (Algebraic.HolomorphicSheafMap.analyticHolomorphicSheafComplex X) r)
    (BrutalCechAcyclicity.Hodge.brutalSheafDirectImageMap_inclusion (Analytification.Base.analytificationMap X) (Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X) r).symm
  exact (Category.assoc _ _ _).trans
    ((congrArg (i ≫ ·) ((Analytic.De.algebraicSheafIntExtensionIso X).inv_hom_id_assoc _)).trans hn)

theorem algebraicHolomorphicTruncationClass_naturality (n : ℕ) (r : ℤ)
    (a : Algebraic.FiltrationExtension.algebraicTruncatedCohomology X n r) :
    Holomorphic.Hypercohomology.algebraicToHolomorphicCohomologyMap X n (Algebraic.FiltrationExtension.algebraicTruncationClass X n r a) =
      holomorphicTruncationClass X n r (Projective.Truncated.algebraicHolomorphicTruncatedCohomologyMap X r (n : ℤ) a) := by
  let f := Analytification.Base.analytificationMap X
  let α := algebraicHolomorphicTruncatedDirectImageInt X r
  let γ := Holomorphic.Int.algebraicToHolomorphicDirectImageInt X
  let e := Algebraic.FiltrationExtension.algebraicTruncationInclusionInt X r
  let d := holomorphicTruncationInclusionInt X r
  have hs := ImageAdjointNaturality.directImageAdjointComplexMap_square f α γ e d (algebraicHolomorphicTruncation_square X r)
  rw [ReferenceDerivedNormalization.algebraicToHolomorphicCohomologyMap_eq_directImage]
  exact CoefficientDerivedNaturality.Ext.coefficientDerivedMap_naturality (TopologicalSheafPullback.sheafInverseImage f)
    (ImageAdjointNaturality.directImageAdjointComplexMap f α) (ImageAdjointNaturality.directImageAdjointComplexMap f γ) e d hs
    (ConstantSheafSections.standardConstantSheaf (TopCat.of X.left)) (ConstantSheafSections.standardConstantSheaf (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
    (TopologicalSheafPullback.constantPullbackIso f).inv (n : ℤ) a

end

end OAI.AlgebraicGeometry.Comparison.Betti.TruncatedNaturality
