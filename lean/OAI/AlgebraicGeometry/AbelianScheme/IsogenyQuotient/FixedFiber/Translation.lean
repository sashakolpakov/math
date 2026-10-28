import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.IntrinsicPair
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.CechCoverTransport

/-! # Translation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.Translation.Construction

noncomputable section

/-! The original fixed-fiber line-logarithm H1 class is the actual
infinitesimal Picard class of translation of the pulled line bundle.
The proof compares the original covers and their actual frame cochains. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj TensorProduct

attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverAffineOpen AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections.familyCoverPairAffineOpen
attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.Fixed.CechCover.fixedFamilyCechCover AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFiberAffineOpen

variable (R : Type) [CommRing R] [Algebra R ℂ] (X : Over (Spec (.of R))) [IsSeparated X.hom]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (C : AbelianModuli.ReferenceFamily.Constructed.LineFrameCover.LineBundleAffineFrameCover L)
    [IsIntegral (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)]
    (v : Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X).hom) → ℂ)

attribute [local instance] IntrinsicChartRange.Construction.fixedTranslationProjectionAffine IntrinsicChartRange.Construction.fixedTranslationFiberSeparated
  IntrinsicChartRange.Construction.fixedTranslationDualDiagonal

theorem fixedFiberLineLogSheafClass_eq_translation :
    AbelianModuli.ReferenceFamily.FixedFiber.LineLogIntrinsicClass.fixedFiberLineLogSheafClass R X C.cover C.transitions
      (AbelianModuli.ReferenceFamily.Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X) v) =
      AbelianModuli.ReferenceFamily.DualLine.ClassKernel.dualLineKernelCohomology (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)
        (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualTranslationLineKernel (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X)
          (L.pullback (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X))
          (AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X) 1 v)) := by
  let G := AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R X
  let p := AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X
  let t := AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv G 1 v
  let f := (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation G t).left
  let g := (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left
  let h := AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation_equal_reduction G t
  let s := fun i => (C.localFrame i).pullbackBy p
  have ha (i : C.cover.I₀) : IsAffineOpen (s i).domain :=
    (isAffineOpen_opensRange (C.cover.f i)).preimage p
  have hs : iSup (fun i => (s i).domain) = ⊤ := AbelianModuli.ReferenceFamily.Fixed.CechCover.fixedFamilyCechCover_covers ℂ R X C.cover
  obtain ⟨hcover, hclosed, hclass⟩ :=
    Intrinsic.FrameReducedPair.Construction.dualLinePullbackDifferenceClass_eq_reducedPair G f g h (L.pullback p) s ha hs
  let d := IntrinsicChartRange.Construction.fixedFiberTranslationFrame R X L C v
  let U := AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechCover G (fun i => (d i).domain)
  let V := AbelianModuli.ReferenceFamily.Fixed.CechCover.fixedFamilyCechCover ℂ R X C.cover
  let pair := Intrinsic.FrameReducedPair.Construction.nativeReducedFramePair G d (IntrinsicChartRange.Construction.fixedFiberTranslationFrame_affine R X L C v)
  let q := AbelianModuli.ReferenceFamily.RegularPair.Closed.regularPairCechCochain G.left U pair
  let he := IntrinsicChartRange.Construction.fixedFiberTranslationFrame_reducedCover R X L C v
  have hV := AbelianModuli.ReferenceFamily.Fixed.CechCover.fixedFamilyCechCover_covers ℂ R X C.cover
  change DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (AbelianModuli.ReferenceFamily.Dual.UnitCechClasses.ringAdditiveSheaf G.left.sheaf).obj U 1 q = 0 at hclosed
  change AbelianModuli.ReferenceFamily.DualLine.PullbackDifference.dualLinePullbackDifferenceClass G f g h (L.pullback p) =
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U (AbelianModuli.ReferenceFamily.Dual.UnitCechClasses.ringAdditiveSheaf G.left.sheaf) hcover 0 q hclosed at hclass
  have ht := Reference.CechCoverTransport.Construction.regularCechCoverTransport_sheafClass G.left he hcover hV q hclosed
  have hq : Reference.CechCoverTransport.Construction.regularCechCoverTransport G.left he q =
      AbelianModuli.ReferenceFamily.RegularPair.Closed.regularPairCechCochain G.left V (IntrinsicChartRange.Construction.fixedFiberIntrinsicTranslationPair R X L C v) :=
    Reference.CechCoverTransport.Construction.regularPairCechCochain_coverTransport G.left he pair
  rw [IntrinsicPair.Construction.fixedFiberIntrinsicTranslationPair_eq_log] at hq
  symm
  change AbelianModuli.ReferenceFamily.DualLine.PullbackDifference.dualLinePullbackDifferenceClass G f g h (L.pullback p) = _
  refine hclass.trans (ht.symm.trans ?_)
  simp only [hq]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.Translation.Construction
