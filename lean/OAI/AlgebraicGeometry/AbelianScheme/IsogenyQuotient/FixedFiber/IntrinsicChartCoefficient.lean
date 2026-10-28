import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.IntrinsicChartRange

/-! # Intrinsic Chart Coefficient -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.IntrinsicChartCoefficient.Construction

noncomputable section

section

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

/-- The actual translated unit is the transition of the native difference frames. -/
theorem fixedFiberIntrinsicChart_unit (i j : C.cover.I₀)
    (hAW :
    let G := AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X
    let V := AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverPairAffineOpen R X C.cover i j
    let B := TranslationLog.Construction.fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V)
    let a : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G := TranslationLog.Construction.fixedFiberCoefficientInclusion R X V
    (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B a).left.opensRange =
      (IntrinsicChartRange.Construction.fixedFiberTranslationFrame R X L C v i).domain ⊓
      (IntrinsicChartRange.Construction.fixedFiberTranslationFrame R X L C v j).domain) :
    let G := AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X
    let V := AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverPairAffineOpen R X C.cover i j
    let B := TranslationLog.Construction.fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V)
    let a : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G := TranslationLog.Construction.fixedFiberCoefficientInclusion R X V
    Units.map (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart.dualAffineTranslationChart_range G B a).symm).toMonoidHom
      (TranslationFrameCoefficients.Construction.translatedFrameTransition G (L.pullback (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X))
        ((C.localFrame i).pullbackBy (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X))
        ((C.localFrame j).pullbackBy (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X))
        (AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv G 1 v) a.left.opensRange
        (TranslationLog.Construction.fixedFiberFrameSupport R X L C V i inf_le_left)
        (TranslationLog.Construction.fixedFiberFrameSupport R X L C V j inf_le_right)) =
      (IntrinsicChartRange.Construction.fixedFiberTranslationFrame R X L C v i).transition
        (IntrinsicChartRange.Construction.fixedFiberTranslationFrame R X L C v j)
        (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B a).left.opensRange
        (hAW.le.trans inf_le_left) (hAW.le.trans inf_le_right) := by
  dsimp only [IntrinsicChartRange.Construction.fixedFiberTranslationFrame]
  exact Intrinsic.FrameOpenTransport.Construction.translatedFrameTransition_on_chart (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)
    (L.pullback (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X))
    ((C.localFrame i).pullbackBy (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X))
    ((C.localFrame j).pullbackBy (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X))
    (AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X) 1 v)
    (TranslationLog.Construction.fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X (AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverPairAffineOpen R X C.cover i j)))
    (TranslationLog.Construction.fixedFiberCoefficientInclusion R X (AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverPairAffineOpen R X C.cover i j))
    (TranslationLog.Construction.fixedFiberFrameSupport R X L C (AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverPairAffineOpen R X C.cover i j) i inf_le_left)
    (TranslationLog.Construction.fixedFiberFrameSupport R X L C (AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverPairAffineOpen R X C.cover i j) j inf_le_right)

end

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

include R X L C v in
abbrev fixedFiberIntrinsicChart_coefficient (i j : C.cover.I₀)
    (hAW :
    let G := AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X
    let V := AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverPairAffineOpen R X C.cover i j
    let B := TranslationLog.Construction.fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V)
    let a : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G := TranslationLog.Construction.fixedFiberCoefficientInclusion R X V
    (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B a).left.opensRange =
      (IntrinsicChartRange.Construction.fixedFiberTranslationFrame R X L C v i).domain ⊓
      (IntrinsicChartRange.Construction.fixedFiberTranslationFrame R X L C v j).domain) := by
  let G := AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X
  let V := AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverPairAffineOpen R X C.cover i j
  let B := TranslationLog.Construction.fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V)
  let a : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G := TranslationLog.Construction.fixedFiberCoefficientInclusion R X V
  let A := (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B a).left.opensRange
  have hu := fixedFiberIntrinsicChart_unit R X L C v i j hAW
  exact congrArg
    (fun u : Γ((AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G).left, A)ˣ =>
      AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFiberTensorInclusion_range R ℂ X V)
        (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (AffinePicardCoefficients.Construction.dualAffineChart_reducedRange G B a)
          (AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv G A
            (isAffineOpen_opensRange (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B a).left) u.val).snd)) hu.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.IntrinsicChartCoefficient.Construction
