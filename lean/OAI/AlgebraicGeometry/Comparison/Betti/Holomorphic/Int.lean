import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SheafFactorization
import OAI.AlgebraicGeometry.Comparison.Betti.ExtensionCoherence

/-! # Int -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.Int

noncomputable section

section

/-! The exact holomorphic factorization retains BettiComparison's original integer-indexed algebraic source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def analyticHolomorphicSheafComplexInt : CochainComplex (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) ℤ :=
  (Algebraic.HolomorphicSheafMap.analyticHolomorphicSheafComplex X).extend (ComplexShape.embeddingUpIntGE 0)

def holomorphicSmoothSheafMapInt : analyticHolomorphicSheafComplexInt X ⟶ Analytic.De.analyticDeRhamSheafComplexInt X :=
  HomologicalComplex.extendMap
    (SheafComplex.inclusionSheafMap (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (ComplexShape.embeddingUpIntGE 0)

def algebraicToHolomorphicDirectImageInt : Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X ⟶
    ((Betti.Smooth.SheafMap.analytificationPushforward X).mapHomologicalComplex (.up ℤ)).obj
      (analyticHolomorphicSheafComplexInt X) :=
  (Analytic.De.algebraicSheafIntExtensionIso X).hom ≫
    HomologicalComplex.extendMap (Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X) (ComplexShape.embeddingUpIntGE 0) ≫
      (Complex.Extension.mapExtendIso (Betti.Smooth.SheafMap.analytificationPushforward X)
        (ComplexShape.embeddingUpIntGE 0) (Algebraic.HolomorphicSheafMap.analyticHolomorphicSheafComplex X)).inv

theorem algebraicToHolomorphicDirectImageInt_factorization :
    algebraicToHolomorphicDirectImageInt X ≫
        ((Betti.Smooth.SheafMap.analytificationPushforward X).mapHomologicalComplex (.up ℤ)).map
          (holomorphicSmoothSheafMapInt X) =
      Analytic.De.algebraicToAnalyticDirectImageInt X := by
  let E := ComplexShape.embeddingUpIntGE 0
  let F := Betti.Smooth.SheafMap.analytificationPushforward X
  let i := SheafComplex.inclusionSheafMap (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  have hn := ExtensionCoherence.Complex.mapExtendIso_inv_naturality F E i
  change (((Analytic.De.algebraicSheafIntExtensionIso X).hom ≫
      HomologicalComplex.extendMap (Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X) E) ≫
      (Complex.Extension.mapExtendIso F E (Algebraic.HolomorphicSheafMap.analyticHolomorphicSheafComplex X)).inv) ≫
        (F.mapHomologicalComplex (.up ℤ)).map (HomologicalComplex.extendMap i E) = _
  erw [Category.assoc, hn, ← Category.assoc]
  erw [Category.assoc (Analytic.De.algebraicSheafIntExtensionIso X).hom
    (HomologicalComplex.extendMap (Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X) E)]
  change ((Analytic.De.algebraicSheafIntExtensionIso X).hom ≫
    ((E.extendFunctor (Algebraic.Sheaves.ComplexSheaves X)).map (Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X) ≫
      (E.extendFunctor (Algebraic.Sheaves.ComplexSheaves X)).map (Algebraic.HolomorphicSheafMap.zariskiHolomorphicSmoothSheafMap X))) ≫ _ = _
  erw [← Functor.map_comp, SheafFactorization.algebraicToHolomorphicSheafMap_factorization]
  rfl

end

/-! The original analytic-site comparison is the composite through the actual holomorphic sheaf complex. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def algebraicToHolomorphicSheafMapInt :
    ((Analytic.De.analytificationInverseImage X).mapHomologicalComplex (.up ℤ)).obj
        (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X) ⟶ analyticHolomorphicSheafComplexInt X :=
  ((Analytic.De.analytificationComplexAdjunctionInt X).homEquiv (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X)
    (analyticHolomorphicSheafComplexInt X)).symm (algebraicToHolomorphicDirectImageInt X)

theorem algebraicToHolomorphicSheafMapInt_normalization :
    (Analytic.De.analytificationComplexAdjunctionInt X).homEquiv (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X)
        (analyticHolomorphicSheafComplexInt X) (algebraicToHolomorphicSheafMapInt X) =
      algebraicToHolomorphicDirectImageInt X :=
  (Analytic.De.analytificationComplexAdjunctionInt X).homEquiv _ _ |>.apply_symm_apply _

theorem algebraicToHolomorphicSheafMapInt_factorization :
    algebraicToHolomorphicSheafMapInt X ≫ holomorphicSmoothSheafMapInt X =
      Analytic.De.algebraicToAnalyticSheafMapInt X := by
  apply ((Analytic.De.analytificationComplexAdjunctionInt X).homEquiv (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X)
    (Analytic.De.analyticDeRhamSheafComplexInt X)).injective
  rw [(Analytic.De.analytificationComplexAdjunctionInt X).homEquiv_naturality_right,
    algebraicToHolomorphicSheafMapInt_normalization,
    Analytic.De.algebraicToAnalyticSheafMapInt_normalization,
    algebraicToHolomorphicDirectImageInt_factorization]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.Int
