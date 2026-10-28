import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ScalarIntegerNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Derived.ComplexSquare
import OAI.AlgebraicGeometry.Comparison.Betti.Derived.ShiftCoherence

/-! # Scalar Derived Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ScalarDerivedNaturality.SectionScalarChange

noncomputable section

/-! Coefficient change and pullback commute on the actual derived de Rham complexes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal

variable {R S : Type} [Field R] [Field S] (σ : R ≃+* S)
  {X Y : Over (Spec (CommRingCat.of S))} (f : X ⟶ Y)

def derivedImageScalarIso :
    Int.derivedInverseImage f ⋙ (SheafScalarChange.SectionScalarChange.sheafRestriction σ X).mapDerivedCategory ≅
      (SheafScalarChange.SectionScalarChange.sheafRestriction σ Y).mapDerivedCategory ⋙ Int.derivedInverseImage (ScalarImage.SectionScalarChange.restrictMap σ f) :=
  AlgebraicGeometry.Comparison.Betti.Derived.FunctorSquare.squareIso (Int.inverseImage f) (SheafScalarChange.SectionScalarChange.sheafRestriction σ X)
    (SheafScalarChange.SectionScalarChange.sheafRestriction σ Y) (Int.inverseImage (ScalarImage.SectionScalarChange.restrictMap σ f)) (ScalarImage.SectionScalarChange.imageScalarIso σ f)

instance derivedImageScalarIso_commShift : NatTrans.CommShift (derivedImageScalarIso σ f).hom ℤ := by
  change NatTrans.CommShift
    ((AlgebraicGeometry.Comparison.Betti.Derived.FunctorComposition.derivedFunctorCompIso (Int.inverseImage f) (SheafScalarChange.SectionScalarChange.sheafRestriction σ X)).hom ≫
      (AlgebraicGeometry.Comparison.Betti.Derived.FunctorIso.functorIso (ScalarImage.SectionScalarChange.imageScalarIso σ f)).hom ≫
        (AlgebraicGeometry.Comparison.Betti.Derived.FunctorComposition.derivedFunctorCompIso (SheafScalarChange.SectionScalarChange.sheafRestriction σ Y)
          (Int.inverseImage (ScalarImage.SectionScalarChange.restrictMap σ f))).inv) ℤ
  infer_instance

theorem derivedComplex_inverse_square :
    (Int.derivedInverseImage (ScalarImage.SectionScalarChange.restrictMap σ f)).map (ScalarChange.SectionScalarChange.derivedComplexIso σ Y).hom ≫
        Int.derivedPullback (ScalarImage.SectionScalarChange.restrictMap σ f) =
      (derivedImageScalarIso σ f).inv.app (DerivedCategory.Q.obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt S Y)) ≫
        (SheafScalarChange.SectionScalarChange.sheafRestriction σ X).mapDerivedCategory.map (Int.derivedPullback f) ≫
          (ScalarChange.SectionScalarChange.derivedComplexIso σ X).hom := by
  apply AlgebraicGeometry.Comparison.Betti.Derived.ComplexSquare.derivedComplexMap_square (Int.inverseImage f) (SheafScalarChange.SectionScalarChange.sheafRestriction σ X)
    (SheafScalarChange.SectionScalarChange.sheafRestriction σ Y) (Int.inverseImage (ScalarImage.SectionScalarChange.restrictMap σ f)) (ScalarImage.SectionScalarChange.imageScalarIso σ f)
    (Int.sheafPullbackInt f) (SheafScalarChange.SectionScalarChange.sheafComplexIntIso σ X).hom (SheafScalarChange.SectionScalarChange.sheafComplexIntIso σ Y).hom
    (Int.sheafPullbackInt (ScalarImage.SectionScalarChange.restrictMap σ f))
  exact CoefficientDiagramTwo.CoefficientDiagram.inverse_left_square
    ((NatIso.mapHomologicalComplex (ScalarImage.SectionScalarChange.imageScalarIso σ f) (ComplexShape.up ℤ)).app
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt S Y)) _ _ (ScalarIntegerNaturality.SectionScalarChange.sheafPullbackInt_square σ f)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ScalarDerivedNaturality.SectionScalarChange
