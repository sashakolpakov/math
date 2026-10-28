import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FrameCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AnalyticFrameTransitions
import OAI.RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation

/-! # Frame Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FrameEvaluation

noncomputable section

/-! Evaluation of ChernClass's genuine frame transitions is evaluation of the
same native regular units used in the theta construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem sectionEvaluationOn_native (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W : X.carrier.Opens)
    (a : Γ(X.carrier, W)) (p : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X W) :
    DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X W a p = RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue p.val.left W p.property a := by
  let q := (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openPointHomeomorph X W).symm p
  have hq : q.left ≫ W.ι = p.val.left :=
    congrArg (fun r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver => r.left)
      (congrArg Subtype.val ((DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openPointHomeomorph X W).apply_symm_apply p))
  have ht : RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue q.left ⊤ (by trivial) (W.topIso.inv a) =
      DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation q (W.topIso.inv a) := by
    have ha : q.left.appLE ⊤ ⊤ (by simp) = q.left.appTop := q.left.appLE_eq_app
    exact congrArg (fun f : Γ(W.toScheme, ⊤) ⟶ Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) =>
      (Scheme.ΓSpecIso (.of ℂ)).hom (f (W.topIso.inv a))) ha
  exact (ht.symm.trans (RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue_open W q.left a).symm).trans
    (RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue_congr _ _ hq W _ p.property a)

theorem framePointTransition_native (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    {M : X.carrier.Modules} (s t : LineFrameAtlas.LocalLineFrame M) (W : X.carrier.Opens)
    (hs : W ≤ s.domain) (ht : W ≤ t.domain) (p : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X W) :
    AnalyticFrameTransitions.framePointTransition X s t p.val (hs p.property) (ht p.property) =
      RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue p.val.left W p.property
        (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit M W
          (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hs s.frame)
          (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization ht t.frame) : Γ(X.carrier, W)) := by
  rw [AnalyticFrameTransitions.framePointTransition_restrict, LineFrameAtlas.LocalLineFrame.transition_native,
    sectionEvaluationOn_native]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FrameEvaluation
