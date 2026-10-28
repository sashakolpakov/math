import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.IntrinsicChartTransport
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.IntrinsicChartCoefficient

/-! # Intrinsic Pair -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.IntrinsicPair.Construction

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

private theorem equality_trans_three {T : Sort*} {a b c d : T}
    (hab : a = b) (hbc : b = c) (hcd : c = d) : a = d :=
  hab.trans (hbc.trans hcd)

include R X L C v in
abbrev fixedFiberIntrinsicTranslationPair_eq_nativePair :=
  funext (fun i => funext (fun j => equality_trans_three
    (IntrinsicChartRange.Construction.fixedFiberIntrinsicTranslationPair_nativeCoefficient R X L C v i j)
    (IntrinsicChartTransport.Construction.fixedFiberIntrinsicChart_transport R X L C v i j)
    (IntrinsicChartCoefficient.Construction.fixedFiberIntrinsicChart_coefficient R X L C v i j
      (IntrinsicChartRange.Construction.fixedFiberIntrinsicChart_range R X L C v i j))))

include R X L C v in
abbrev fixedFiberIntrinsicTranslationPair_eq_log :=
  (fixedFiberIntrinsicTranslationPair_eq_nativePair R X L C v).trans
    (PicardPairClass.Construction.fixedFiberNativePicardPair_eq_log R X L C v)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.IntrinsicPair.Construction
