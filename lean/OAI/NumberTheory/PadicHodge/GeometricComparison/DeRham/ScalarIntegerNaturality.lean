import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ScalarNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExtensionComposition

/-! # Scalar Integer Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ScalarIntegerNaturality.SectionScalarChange

noncomputable section

/-! The native integer de Rham complexes retain the coefficient/pullback square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal

variable {R S : Type} [Field R] [Field S] (σ : R ≃+* S)
  {X Y : Over (Spec (CommRingCat.of S))} (f : X ⟶ Y)

theorem sheafPullbackInt_square :
    ((SheafScalarChange.SectionScalarChange.sheafRestriction σ X).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (Int.sheafPullbackInt f) ≫ (SheafScalarChange.SectionScalarChange.sheafComplexIntIso σ X).hom =
      (NatTrans.mapHomologicalComplex (ScalarImage.SectionScalarChange.imageScalarIso σ f).hom (ComplexShape.up ℤ)).app
          (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt S Y) ≫
        ((Int.inverseImage (ScalarImage.SectionScalarChange.restrictMap σ f)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (SheafScalarChange.SectionScalarChange.sheafComplexIntIso σ Y).hom ≫ Int.sheafPullbackInt (ScalarImage.SectionScalarChange.restrictMap σ f) := by
  apply ExtensionComposition.FormsAdapter.extendedFourFunctor_square (Int.inverseImage f) (SheafScalarChange.SectionScalarChange.sheafRestriction σ X)
    (SheafScalarChange.SectionScalarChange.sheafRestriction σ Y) (Int.inverseImage (ScalarImage.SectionScalarChange.restrictMap σ f)) (ScalarImage.SectionScalarChange.imageScalarIso σ f)
    (Int.sheafPullback f) (SheafScalarChange.SectionScalarChange.sheafComplexIso σ X).hom (SheafScalarChange.SectionScalarChange.sheafComplexIso σ Y).hom
    (Int.sheafPullback (ScalarImage.SectionScalarChange.restrictMap σ f)) ComplexShape.embeddingUpNat
  rw [ScalarImage.SectionScalarChange.imageScalarIso_onComplexes]
  exact ScalarNaturality.SectionScalarChange.sheafPullback_square σ f

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ScalarIntegerNaturality.SectionScalarChange
