import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.PicardCoordinates

/-! # Picard Log -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.PicardLog.Construction

noncomputable section

section

/-! Compare the actual translated-frame Picard coefficient with the original logarithm.
The coordinate transport steps are cached in the imported helper modules. -/

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

theorem fixedFiberPicardCoefficient_eq_originalLog :
    let G := AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X
    let B := TranslationLog.Construction.fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V)
    let a : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G := TranslationLog.Construction.fixedFiberCoefficientInclusion R X V
    let p := AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X
    let s := (C.localFrame i).pullbackBy p
    let t := (C.localFrame j).pullbackBy p
    let hR := AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFiberTensorInclusion_range R ℂ X V
    let u := Units.map (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart.dualAffineTranslationChart_range G B a).symm).toMonoidHom
      (TranslationFrameCoefficients.Construction.translatedFrameTransition G (L.pullback p) s t (AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv G 1 v)
        a.left.opensRange (TranslationLog.Construction.fixedFiberFrameSupport R X L C V i hi) (TranslationLog.Construction.fixedFiberFrameSupport R X L C V j hj))
    AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hR
      (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (AffinePicardCoefficients.Construction.dualAffineChart_reducedRange G B a)
        (AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv G (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B a).left.opensRange
          (isAffineOpen_opensRange (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B a).left) u.val).snd) =
      AbelianModuli.ReferenceFamily.FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R ℂ X V
        (AbelianModuli.ReferenceFamily.FixedFiber.LineLogCocycle.fixedFiberLineLogCoefficient R X (fun b => (C.cover.f b).opensRange) C.transitions
          (AbelianModuli.ReferenceFamily.Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear G v) V i j hi hj) := by
  exact PicardCoordinates.Construction.fixedPicardCoefficient_from_coordinates (R := R) (X := X) (V := V) _ _
    (TranslationLog.Construction.fixedFiberLineLogCoefficient_eq_translationCoefficient R X L C V i j hi hj v)

end

section

/-! The native fixed-fiber Picard log section and its logarithm formula. -/

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

/-- The actual native Picard coefficient as a regular section on the
original fixed-fiber open. This definition uses the pulled frames and
scheme coefficient maps, before invoking the logarithm comparison. -/
def fixedFiberPicardLogSection :
    Γ((AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).left, AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFiberAffineOpen R ℂ X V) :=
  let G := AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X
  let B := TranslationLog.Construction.fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V)
  let a : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G := TranslationLog.Construction.fixedFiberCoefficientInclusion R X V
  let p := AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X
  let s := (C.localFrame i).pullbackBy p
  let t := (C.localFrame j).pullbackBy p
  let hR := AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFiberTensorInclusion_range R ℂ X V
  let u := Units.map (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart.dualAffineTranslationChart_range G B a).symm).toMonoidHom
    (TranslationFrameCoefficients.Construction.translatedFrameTransition G (L.pullback p) s t (AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv G 1 v)
      a.left.opensRange (TranslationLog.Construction.fixedFiberFrameSupport R X L C V i hi) (TranslationLog.Construction.fixedFiberFrameSupport R X L C V j hj))
  AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hR
    (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (AffinePicardCoefficients.Construction.dualAffineChart_reducedRange G B a)
      (AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv G (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B a).left.opensRange
        (isAffineOpen_opensRange (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B a).left) u.val).snd)

end

/-! The native fixed-fiber Picard log section and its logarithm formula. -/

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

include R X L C V i j hi hj v in
abbrev fixedFiberPicardLogSection_eq :=
  fixedFiberPicardCoefficient_eq_originalLog R X L C V i j hi hj v

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.PicardLog.Construction
