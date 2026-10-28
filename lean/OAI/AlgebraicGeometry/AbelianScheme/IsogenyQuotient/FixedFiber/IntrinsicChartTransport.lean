import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.IntrinsicChartRange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.FrameOpenTransportSquare

/-! # Intrinsic Chart Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.IntrinsicChartTransport.Construction

noncomputable section

/-! The intrinsic pair coefficients of the actual translated pulled
frames agree with the original fixed-fiber line-logarithm pair. The
cover equality and every intervening open equality are constructed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] AffinePicardCoefficients.Construction.affinePicardDualIsAffine TranslationLog.Construction.nativeFixedFiberOpen
attribute [local instance] IntrinsicChartRange.Construction.fixedTranslationProjectionAffine IntrinsicChartRange.Construction.fixedTranslationFiberSeparated IntrinsicChartRange.Construction.fixedTranslationDualDiagonal

attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverAffineOpen AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverPairAffineOpen
attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.Fixed.CechCover.fixedFamilyCechCover AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFiberAffineOpen
attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.FixedFiber.AffineDiagram.fixedFiberTensorDiagram AbelianModuli.ReferenceFamily.FixedFiber.AffineDiagram.fixedFiberTensorAlgebras
attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.Affine.OpenDiagram.familyAffineCoordinateFunctor AbelianModuli.HilbertConstruction.Affine.CoordinateFunctor.affineCoordinateFunctor AbelianModuli.HilbertConstruction.AlgebraTensorFunctor.algebraTensorFunctor

variable (R : Type) [CommRing R] [Algebra R ℂ] (X : Over (Spec (.of R))) [IsSeparated X.hom]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (C : AbelianModuli.ReferenceFamily.Constructed.LineFrameCover.LineBundleAffineFrameCover L)
    [IsIntegral (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)]
    (v : Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).hom) → ℂ)

theorem fixedFiberIntrinsicChart_transport (i j : C.cover.I₀) :
    let G := AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X
    let V := AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverPairAffineOpen R X C.cover i j
    let B := TranslationLog.Construction.fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V)
    let a : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G := TranslationLog.Construction.fixedFiberCoefficientInclusion R X V
    let d := IntrinsicChartRange.Construction.fixedFiberTranslationFrame R X L C v
    let A := (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B a).left.opensRange
    let W := (d i).domain ⊓ (d j).domain
    let hAW := IntrinsicChartRange.Construction.fixedFiberIntrinsicChart_range R X L C v i j
    let hcover := congrArg (fun U => U i ⊓ U j) (IntrinsicChartRange.Construction.fixedFiberTranslationFrame_reducedCover R X L C v)
    AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hcover
      (AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv G W
        ((IntrinsicChartRange.Construction.fixedFiberTranslationFrame_affine R X L C v i).inf (IntrinsicChartRange.Construction.fixedFiberTranslationFrame_affine R X L C v j))
        ((d i).transition (d j) W inf_le_left inf_le_right).val).snd =
      AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFiberTensorInclusion_range R ℂ X V)
        (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (AffinePicardCoefficients.Construction.dualAffineChart_reducedRange G B a)
          (AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv G A
            (isAffineOpen_opensRange (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B a).left)
            ((d i).transition (d j) A (hAW.le.trans inf_le_left) (hAW.le.trans inf_le_right)).val).snd) := by
  exact Intrinsic.FrameOpenTransportSquare.Construction.nativeFrameOpenCoefficient_transport_square (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)
    (IntrinsicChartRange.Construction.fixedFiberTranslationFrame R X L C v i) (IntrinsicChartRange.Construction.fixedFiberTranslationFrame R X L C v j)
    (IntrinsicChartRange.Construction.fixedFiberIntrinsicChart_range R X L C v i j)
    (isAffineOpen_opensRange (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X) (TranslationLog.Construction.fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X (AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverPairAffineOpen R X C.cover i j))) (TranslationLog.Construction.fixedFiberCoefficientInclusion R X (AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverPairAffineOpen R X C.cover i j))).left)
    ((IntrinsicChartRange.Construction.fixedFiberTranslationFrame_affine R X L C v i).inf (IntrinsicChartRange.Construction.fixedFiberTranslationFrame_affine R X L C v j))
    ((IntrinsicChartRange.Construction.fixedFiberIntrinsicChart_range R X L C v i j).le.trans inf_le_left) ((IntrinsicChartRange.Construction.fixedFiberIntrinsicChart_range R X L C v i j).le.trans inf_le_right)
    inf_le_left inf_le_right
    (AffinePicardCoefficients.Construction.dualAffineChart_reducedRange (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X) (TranslationLog.Construction.fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X (AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverPairAffineOpen R X C.cover i j))) (TranslationLog.Construction.fixedFiberCoefficientInclusion R X (AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverPairAffineOpen R X C.cover i j)))
    (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFiberTensorInclusion_range R ℂ X (AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverPairAffineOpen R X C.cover i j))
    (congrArg (fun U => U i ⊓ U j) (IntrinsicChartRange.Construction.fixedFiberTranslationFrame_reducedCover R X L C v))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.IntrinsicChartTransport.Construction
