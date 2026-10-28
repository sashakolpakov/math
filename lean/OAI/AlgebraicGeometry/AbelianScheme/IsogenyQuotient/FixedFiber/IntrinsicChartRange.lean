import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.FrameReducedPair
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.FrameOpenTransport
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.PicardPairClass
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProjectionReducedCover
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.AffineDiagonal

/-! # Intrinsic Chart Range -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.IntrinsicChartRange.Construction

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

attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverAffineOpen AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverPairAffineOpen
attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.Fixed.CechCover.fixedFamilyCechCover AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFiberAffineOpen
attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.FixedFiber.AffineDiagram.fixedFiberTensorDiagram AbelianModuli.ReferenceFamily.FixedFiber.AffineDiagram.fixedFiberTensorAlgebras
attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.Affine.OpenDiagram.familyAffineCoordinateFunctor AbelianModuli.HilbertConstruction.Affine.CoordinateFunctor.affineCoordinateFunctor AbelianModuli.HilbertConstruction.AlgebraTensorFunctor.algebraTensorFunctor

variable (R : Type) [CommRing R] [Algebra R ℂ] (X : Over (Spec (.of R))) [IsSeparated X.hom]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (C : AbelianModuli.ReferenceFamily.Constructed.LineFrameCover.LineBundleAffineFrameCover L)
    [IsIntegral (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)]
    (v : Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).hom) → ℂ)

local instance fixedTranslationProjectionAffine : IsAffineHom (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X) := by
  change IsAffineHom (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
  exact MorphismProperty.pullback_fst _ _
    (inferInstance : IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))

local instance fixedTranslationFiberSeparated : IsSeparated (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).hom := by
  change IsSeparated (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
  infer_instance

local instance fixedTranslationDualDiagonal :
    IsAffineHom (pullback.diagonal (terminal.from (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).left)) :=
  AbelianModuli.ReferenceFamily.Dual.AffineDiagonal.dualFamily_affineDiagonal (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)

def fixedFiberTranslationFrame (i : C.cover.I₀) :
    AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame (AbelianModuli.ReferenceFamily.DualLine.PullbackDifference.dualLinePullbackDifference (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)
      (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)
        (AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X) 1 v)).left
      (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)).left
      (L.pullback (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X))).sheaf :=
  AbelianModuli.ReferenceFamily.Dual.DifferenceOpenFrames.dualDifferenceOpenFrame (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)
    (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)
      (AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X) 1 v)).left
    (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)).left
    (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation_equal_reduction (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)
      (AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X) 1 v))
    (L.pullback (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X)) ((C.localFrame i).pullbackBy (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X))

omit [IsSeparated X.hom] in
theorem fixedFiberTranslationFrame_affine (i : C.cover.I₀) :
    IsAffineOpen (fixedFiberTranslationFrame R X L C v i).domain :=
  ((isAffineOpen_opensRange (C.cover.f i)).preimage (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X)).preimage
    (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)).left

omit [IsSeparated X.hom] in
theorem fixedFiberTranslationFrame_reducedCover :
    AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechCover (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)
      (fun i => (fixedFiberTranslationFrame R X L C v i).domain) =
      AbelianModuli.ReferenceFamily.Fixed.CechCover.fixedFamilyCechCover ℂ R X C.cover :=
  AbelianModuli.ReferenceFamily.Dual.ProjectionReducedCover.dualProjectionReducedCover (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X) (AbelianModuli.ReferenceFamily.Fixed.CechCover.fixedFamilyCechCover ℂ R X C.cover)

def fixedFiberIntrinsicTranslationPair (i j : C.cover.I₀) :
    Γ((AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).left,
      AbelianModuli.ReferenceFamily.Fixed.CechCover.fixedFamilyCechCover ℂ R X C.cover i ⊓ AbelianModuli.ReferenceFamily.Fixed.CechCover.fixedFamilyCechCover ℂ R X C.cover j) :=
  AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (congrArg (fun W => W i ⊓ W j)
    (fixedFiberTranslationFrame_reducedCover R X L C v))
    (Intrinsic.FrameReducedPair.Construction.nativeReducedFramePair (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X) (fixedFiberTranslationFrame R X L C v)
      (fixedFiberTranslationFrame_affine R X L C v) i j)

/-- The named intrinsic pair is its literal native coefficient on the frame overlap. -/
theorem fixedFiberIntrinsicTranslationPair_nativeCoefficient (i j : C.cover.I₀) :
    let G := AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X
    let d := fixedFiberTranslationFrame R X L C v
    let W := (d i).domain ⊓ (d j).domain
    let hcover := congrArg (fun U => U i ⊓ U j)
      (fixedFiberTranslationFrame_reducedCover R X L C v)
    fixedFiberIntrinsicTranslationPair R X L C v i j =
      AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hcover
        (AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv G W
          ((fixedFiberTranslationFrame_affine R X L C v i).inf
            (fixedFiberTranslationFrame_affine R X L C v j))
          ((d i).transition (d j) W inf_le_left inf_le_right).val).snd := by
  dsimp only
  unfold fixedFiberIntrinsicTranslationPair Intrinsic.FrameReducedPair.Construction.nativeReducedFramePair
  rfl

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
attribute [local instance] fixedTranslationProjectionAffine fixedTranslationFiberSeparated fixedTranslationDualDiagonal

attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverAffineOpen AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverPairAffineOpen
attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.Fixed.CechCover.fixedFamilyCechCover AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFiberAffineOpen
attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.FixedFiber.AffineDiagram.fixedFiberTensorDiagram AbelianModuli.ReferenceFamily.FixedFiber.AffineDiagram.fixedFiberTensorAlgebras
attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.Affine.OpenDiagram.familyAffineCoordinateFunctor AbelianModuli.HilbertConstruction.Affine.CoordinateFunctor.affineCoordinateFunctor AbelianModuli.HilbertConstruction.AlgebraTensorFunctor.algebraTensorFunctor

variable (R : Type) [CommRing R] [Algebra R ℂ] (X : Over (Spec (.of R))) [IsSeparated X.hom]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (C : AbelianModuli.ReferenceFamily.Constructed.LineFrameCover.LineBundleAffineFrameCover L)
    [IsIntegral (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)]
    (v : Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).hom) → ℂ)

/-- The affine tensor chart is exactly the overlap of the actual translated frames. -/
theorem fixedFiberIntrinsicChart_range (i j : C.cover.I₀) :
    let G := AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X
    let V := AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverPairAffineOpen R X C.cover i j
    let B := TranslationLog.Construction.fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V)
    let a : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G := TranslationLog.Construction.fixedFiberCoefficientInclusion R X V
    (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B a).left.opensRange =
      (fixedFiberTranslationFrame R X L C v i).domain ⊓
      (fixedFiberTranslationFrame R X L C v j).domain := by
  let G := AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X
  let V := AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverPairAffineOpen R X C.cover i j
  let B := TranslationLog.Construction.fixedFiberCoefficientAlgebra (ℂ ⊗[R] AbelianModuli.ReferenceFamily.Family.AffineTangentLifts.familyAffineRing R X V)
  let a : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G := TranslationLog.Construction.fixedFiberCoefficientInclusion R X V
  have hR : a.left.opensRange = AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFiberAffineOpen R ℂ X V :=
    AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFiberTensorInclusion_range R ℂ X V
  change (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B a).left.opensRange = _
  rw [AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart.dualAffineTranslationChart_range G B a, hR]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.IntrinsicChartRange.Construction
