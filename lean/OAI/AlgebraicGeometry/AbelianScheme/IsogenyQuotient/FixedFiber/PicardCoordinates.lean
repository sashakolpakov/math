import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.PicardCoefficientTransport
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.TranslationLog

/-! # Picard Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.PicardCoordinates.Construction

noncomputable section

/-! Fixed-fiber coordinate comparison, independent of the translated frame input. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber AbelianModuli.ReferenceFamily.FixedFiber.AffineDiagram.fixedFiberTensorDiagram AbelianModuli.ReferenceFamily.FixedFiber.AffineDiagram.fixedFiberTensorAlgebras
attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.Affine.OpenDiagram.familyAffineCoordinateFunctor AbelianModuli.HilbertConstruction.Affine.CoordinateFunctor.affineCoordinateFunctor AbelianModuli.HilbertConstruction.AlgebraTensorFunctor.algebraTensorFunctor

variable (R : Type) [CommRing R] [Algebra R ℂ] (X : Over (Spec (.of R)))
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (C : AbelianModuli.ReferenceFamily.Constructed.LineFrameCover.LineBundleAffineFrameCover L)
    (V : X.left.affineOpens) (i j : C.cover.I₀)
    (hi : V.1 ≤ (C.cover.f i).opensRange) (hj : V.1 ≤ (C.cover.f j).opensRange)
    [IsIntegral (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)]
    (v : Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).hom) → ℂ)

attribute [local instance] TranslationLog.Construction.nativeFixedFiberOpen AffinePicardCoefficients.Construction.affinePicardDualIsAffine

omit [IsIntegral (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).left]
  [Smooth (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).hom] [GrpObj (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)] in
private theorem fixedPicardRegularSection_formula (c : ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V) :
    AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFiberTensorInclusion_range R ℂ X V)
      (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ
        (TranslationLog.Construction.fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V))
        (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X) (TranslationLog.Construction.fixedFiberCoefficientInclusion R X V) c) =
      AbelianModuli.ReferenceFamily.FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R ℂ X V c := rfl

omit [IsIntegral (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).left]
  [Smooth (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).hom] [GrpObj (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)] in
theorem fixedPicardCoefficient_from_coordinates
    (u : Γ((AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).left,
      (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)
        (TranslationLog.Construction.fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V))
        (TranslationLog.Construction.fixedFiberCoefficientInclusion R X V)).left.opensRange)ˣ)
    (c : ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V)
    (hn : (Units.map (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ
      (CommAlgCat.of ℂ (DualNumber (TranslationLog.Construction.fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V))))
      (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)
      (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)
        (TranslationLog.Construction.fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V))
        (TranslationLog.Construction.fixedFiberCoefficientInclusion R X V))).symm.toMonoidHom u).val.snd = c) :
    let G := AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X
    let B := TranslationLog.Construction.fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V)
    let a : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G := TranslationLog.Construction.fixedFiberCoefficientInclusion R X V
    AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFiberTensorInclusion_range R ℂ X V)
      (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (AffinePicardCoefficients.Construction.dualAffineChart_reducedRange G B a)
        (AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv G (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B a).left.opensRange
          (isAffineOpen_opensRange (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B a).left) u.val).snd) =
      AbelianModuli.ReferenceFamily.FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R ℂ X V c := by
  have h := Intrinsic.PicardCoefficientTransport.Construction.nativePicardCoefficient_from_coordinates (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)
    (TranslationLog.Construction.fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V))
    (TranslationLog.Construction.fixedFiberCoefficientInclusion R X V) u c hn
  exact (congrArg (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFiberTensorInclusion_range R ℂ X V)) h).trans
    (fixedPicardRegularSection_formula R X V c)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.PicardCoordinates.Construction
