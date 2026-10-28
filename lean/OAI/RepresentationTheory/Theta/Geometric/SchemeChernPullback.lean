import OAI.RepresentationTheory.Theta.Geometric.SchemeAtlasFrames
import OAI.RepresentationTheory.Theta.Geometric.SchemeFramePullback
import OAI.RepresentationTheory.Theta.Geometric.CocycleClassNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.ChernComparison

/-! # Scheme Chern Pullback -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! On an actual smooth projective fiber, pulling the total scheme's
transition cocycle computes the original native algebraic Chern class. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left} (A : SchemeLineFrame.SchemeLineAtlas L)

theorem SchemeLineFrame.SchemeLineAtlas.pullback_chernClass_native (Y : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (f : Y.toOver ⟶ X) :
    (A.continuousCocycle.pullback (TopCat.ofHom (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f))).chernClass =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass Y (L.pullback f.left) := by
  let C := A.continuousCocycle.pullback (TopCat.ofHom (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f))
  let r (i : C.LogIndex) := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.PullbackFrames.pullbackLocalFrame f.left L.sheaf (A.localFrame (C.logParent i))
  have hr : ∀ i, C.logCover i ≤ AlgebraicGeometry.AbelianModuli.ReferenceFamily.AnalyticFrameTransitions.frameAnalyticOpen Y (r i) := by
    intro i p hp
    exact C.logCover_subset i hp
  apply (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.ChernComparison.firstChernClass_eq_frameLogs (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.nativeLineBundle Y (L.pullback f.left))
    C.logCover C.logCover_covers r hr C.logarithm C.logarithm_cocycle ?_).symm
  intro a p
  have he := (C.exp_logarithm a p).trans (C.transition_eq_point (C.logParent ∘ a) _)
  have ha := A.pointTransition_eq_frame (C.logParent (a 0)) (C.logParent (a 1))
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p.val)
    (C.logCover_subset (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le C.logCover a 0 p.property))
    (C.logCover_subset (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le C.logCover a 1 p.property))
  have hp := SchemeFramePullback.SchemeFrames.pullbackFrame_pointTransition f
    (A.localFrame (C.logParent (a 0))) (A.localFrame (C.logParent (a 1))) p.val
    (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le C.logCover a 0 p.property))
    (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le C.logCover a 1 p.property))
  exact he.trans (ha.trans (hp.symm.trans (SchemeAtlasFrames.schemeFrame_pointTransition_native Y _ _ p.val _ _)))

theorem SchemeLineFrame.SchemeLineAtlas.pullback_chernClass_native_compact (Y : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (f : Y.toOver ⟶ X) {T : TopCat} [CompactSpace T] [NormalSpace T]
    (q : T ⟶ TopCat.of (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y.toOver)) :
    (A.continuousCocycle.pullback
      (q ≫ TopCat.ofHom (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f))).chernClass =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) q 2
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass Y (L.pullback f.left)) := by
  rw [← ContinuousLine.ContinuousLineCocycle.pullback_comp, ContinuousLine.ContinuousLineCocycle.chernClass_pullback,
    A.pullback_chernClass_native Y f]

end

end OAI.RepresentationTheory.Theta.Geometric
