import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ScalarDerivedNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantScalar
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.Composition
import OAI.AlgebraicGeometry.Comparison.Betti.Derived.SingleSquare

/-! # Scalar Cohomology Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ScalarCohomologyNaturality.SectionScalarChange

noncomputable section

/-! Naturality of the actual semilinear coefficient-change equivalence on native de Rham cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal

variable {R S : Type} [Field R] [Field S] (σ : R ≃+* S)

theorem cohomologyEquiv_transport (X : Over (Spec (CommRingCat.of S))) (n : ℕ)
    (a : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology S X n) :
    ScalarChange.SectionScalarChange.cohomologyEquiv σ X n a = AlgebraicGeometry.Comparison.Betti.ShiftedHomSquare.transport (SheafScalarChange.SectionScalarChange.sheafRestriction σ X).mapDerivedCategory
      (ScalarChange.SectionScalarChange.derivedCoefficientIso σ X) (ScalarChange.SectionScalarChange.derivedComplexIso σ X).hom a := by
  change ((ScalarChange.SectionScalarChange.derivedCoefficientIso σ X).inv ≫ (SheafScalarChange.SectionScalarChange.sheafRestriction σ X).mapDerivedCategory.map a) ≫
    (ScalarChange.SectionScalarChange.derivedShiftedComplexIso σ X n).hom = _
  simp only [ScalarChange.SectionScalarChange.derivedShiftedComplexIso, Iso.trans_hom, Functor.mapIso_hom,
    AlgebraicGeometry.Comparison.Betti.ShiftedHomSquare.transport, ShiftedHom.map, Category.assoc]
  rfl

variable {X Y : Over (Spec (CommRingCat.of S))} (f : X ⟶ Y)

theorem derivedCoefficient_square :
    (SheafScalarChange.SectionScalarChange.sheafRestriction σ X).mapDerivedCategory.map (Int.derivedConstantIso f).hom ≫
        (ScalarChange.SectionScalarChange.derivedCoefficientIso σ X).hom =
      (ScalarDerivedNaturality.SectionScalarChange.derivedImageScalarIso σ f).hom.app
          ((DerivedCategory.singleFunctor (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves S Y) 0).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf S Y)) ≫
        (Int.derivedInverseImage (ScalarImage.SectionScalarChange.restrictMap σ f)).map (ScalarChange.SectionScalarChange.derivedCoefficientIso σ Y).hom ≫
          (Int.derivedConstantIso (ScalarImage.SectionScalarChange.restrictMap σ f)).hom := by
  have hs := CoefficientDiagramTwo.CoefficientDiagram.inverse_left_square
    ((ScalarImage.SectionScalarChange.imageScalarIso σ f).app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf S Y)) _ _ (ConstantScalar.SectionScalarChange.coefficientSheafIso_square σ f)
  have h := AlgebraicGeometry.Comparison.Betti.Derived.SingleSquare.derivedSingleMap_square (Int.inverseImage f) (SheafScalarChange.SectionScalarChange.sheafRestriction σ X)
    (SheafScalarChange.SectionScalarChange.sheafRestriction σ Y) (Int.inverseImage (ScalarImage.SectionScalarChange.restrictMap σ f)) (ScalarImage.SectionScalarChange.imageScalarIso σ f)
    (Int.inverseImageConstantIso f).hom (SheafScalarChange.SectionScalarChange.coefficientSheafIso σ X).hom
    (SheafScalarChange.SectionScalarChange.coefficientSheafIso σ Y).hom (Int.inverseImageConstantIso (ScalarImage.SectionScalarChange.restrictMap σ f)).hom hs
  exact CoefficientDiagramTwo.CoefficientDiagram.inverse_left_square
    ((ScalarDerivedNaturality.SectionScalarChange.derivedImageScalarIso σ f).app
      ((DerivedCategory.singleFunctor (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves S Y) 0).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf S Y))).symm _ _ h

theorem cohomologyEquiv_naturality (n : ℕ) (a : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology S Y n) :
    ScalarChange.SectionScalarChange.cohomologyEquiv σ X n (Int.pullback f n a) =
      Int.pullback (ScalarImage.SectionScalarChange.restrictMap σ f) n (ScalarChange.SectionScalarChange.cohomologyEquiv σ Y n a) := by
  have h := AlgebraicGeometry.Comparison.Betti.ShiftedHomSquare.transport_square (Int.derivedInverseImage f)
    (SheafScalarChange.SectionScalarChange.sheafRestriction σ X).mapDerivedCategory (SheafScalarChange.SectionScalarChange.sheafRestriction σ Y).mapDerivedCategory
    (Int.derivedInverseImage (ScalarImage.SectionScalarChange.restrictMap σ f)) (ScalarDerivedNaturality.SectionScalarChange.derivedImageScalarIso σ f)
    (Int.derivedConstantIso f) (ScalarChange.SectionScalarChange.derivedCoefficientIso σ X)
    (ScalarChange.SectionScalarChange.derivedCoefficientIso σ Y) (Int.derivedConstantIso (ScalarImage.SectionScalarChange.restrictMap σ f))
    (Int.derivedPullback f) (ScalarChange.SectionScalarChange.derivedComplexIso σ X).hom
    (ScalarChange.SectionScalarChange.derivedComplexIso σ Y).hom (Int.derivedPullback (ScalarImage.SectionScalarChange.restrictMap σ f))
    (derivedCoefficient_square σ f) (ScalarDerivedNaturality.SectionScalarChange.derivedComplex_inverse_square σ f) a
  have hl := (cohomologyEquiv_transport σ X n (Int.pullback f n a)).trans
    (congrArg (AlgebraicGeometry.Comparison.Betti.ShiftedHomSquare.transport (SheafScalarChange.SectionScalarChange.sheafRestriction σ X).mapDerivedCategory
      (ScalarChange.SectionScalarChange.derivedCoefficientIso σ X) (ScalarChange.SectionScalarChange.derivedComplexIso σ X).hom)
        (Composition.pullback_transport f n a))
  have hr := (Composition.pullback_transport (ScalarImage.SectionScalarChange.restrictMap σ f) n (ScalarChange.SectionScalarChange.cohomologyEquiv σ Y n a)).trans
    (congrArg (AlgebraicGeometry.Comparison.Betti.ShiftedHomSquare.transport (Int.derivedInverseImage (ScalarImage.SectionScalarChange.restrictMap σ f))
      (Int.derivedConstantIso (ScalarImage.SectionScalarChange.restrictMap σ f)) (Int.derivedPullback (ScalarImage.SectionScalarChange.restrictMap σ f)))
        (cohomologyEquiv_transport σ Y n a))
  exact hl.trans (h.trans hr.symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ScalarCohomologyNaturality.SectionScalarChange
