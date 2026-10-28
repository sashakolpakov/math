import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.NaturalityInt
import OAI.AlgebraicGeometry.Comparison.Betti.AdjunctionComplexUniqueness
import OAI.AlgebraicGeometry.Comparison.Betti.AdjunctionExtension

/-! # Inverse Naturality Int -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytic.InverseNaturalityInt

noncomputable section

/-! The direct-image realization square gives the actual inverse-image square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)

def schemeAnalyticImageAdjunctionInt :
    (TopologicalSheafPullback.sheafInverseImage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⊣
      (TopologicalSheafPullback.sheafDirectImage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ) :=
  Complex.Adjunction.onComplexes
    (TopologicalSheafPullback.sheafImageAdjunction (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)) (ComplexShape.up ℤ)

/-- The canonical mate of the actual commuting square of direct images. -/
def analytificationComplexMateIso :
    (Algebraic.Sheaves.inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (De.analytificationInverseImage X).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (De.analytificationInverseImage Y).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (TopologicalSheafPullback.sheafInverseImage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).mapHomologicalComplex
          (ComplexShape.up ℤ) :=
  ((OpenForms.imageComplexAdjunctionInt f).comp (De.analytificationComplexAdjunctionInt X)).leftAdjointUniq
    ((De.analytificationComplexAdjunctionInt Y).comp (schemeAnalyticImageAdjunctionInt f))

variable [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

def schemeAnalyticDeRhamPullbackInt :
    ((TopologicalSheafPullback.sheafInverseImage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (De.analyticDeRhamSheafComplexInt Y) ⟶ De.analyticDeRhamSheafComplexInt X :=
  ((schemeAnalyticImageAdjunctionInt f).homEquiv _ _).symm (NaturalityInt.schemeAnalyticDeRhamDirectImageInt f)

theorem schemeAnalyticDeRhamPullbackInt_normalization :
    (schemeAnalyticImageAdjunctionInt f).homEquiv _ _ (schemeAnalyticDeRhamPullbackInt f) =
      NaturalityInt.schemeAnalyticDeRhamDirectImageInt f :=
  (schemeAnalyticImageAdjunctionInt f).homEquiv _ _ |>.apply_symm_apply _

theorem algebraicToAnalyticSheafMapInt_naturality :
    ((TopologicalSheafPullback.sheafInverseImage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (De.algebraicToAnalyticSheafMapInt Y) ≫
        schemeAnalyticDeRhamPullbackInt f =
    (analytificationComplexMateIso f).inv.app (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt Y) ≫
      ((De.analytificationInverseImage X).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (OpenForms.deRhamSheafPullbackInt f) ≫ De.algebraicToAnalyticSheafMapInt X := by
  let a := OpenForms.imageComplexAdjunctionInt f
  let b := De.analytificationComplexAdjunctionInt X
  let c := De.analytificationComplexAdjunctionInt Y
  let d := schemeAnalyticImageAdjunctionInt f
  let K := Algebraic.Sheaves.algebraicDeRhamSheafComplexInt Y
  let L := De.analyticDeRhamSheafComplexInt X
  apply ((c.comp d).homEquiv K L).injective
  have hp : a.homEquiv _ _ (OpenForms.deRhamSheafPullbackInt f) = OpenForms.deRhamSheafDirectImageInt f :=
    (a.homEquiv _ _).apply_symm_apply _
  erw [AdjunctionComplexUniqueness.comp_homEquiv_map_comp c d
    (De.algebraicToAnalyticSheafMapInt Y) (schemeAnalyticDeRhamPullbackInt f),
    De.algebraicToAnalyticSheafMapInt_normalization Y,
    schemeAnalyticDeRhamPullbackInt_normalization f]
  change _ = (c.comp d).homEquiv K L
    (((a.comp b).leftAdjointUniq (c.comp d)).inv.app K ≫
      ((De.analytificationInverseImage X).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (OpenForms.deRhamSheafPullbackInt f) ≫ De.algebraicToAnalyticSheafMapInt X)
  erw [AdjunctionComplexUniqueness.leftAdjointUniq_inv_homEquiv (a.comp b) (c.comp d),
    AdjunctionComplexUniqueness.comp_homEquiv_map_comp a b
      (OpenForms.deRhamSheafPullbackInt f) (De.algebraicToAnalyticSheafMapInt X), hp,
    De.algebraicToAnalyticSheafMapInt_normalization X]
  exact NaturalityInt.algebraicToAnalyticDirectImageInt_naturality f

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytic.InverseNaturalityInt
