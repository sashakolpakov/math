import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.FrameCoordinates
import OAI.RepresentationTheory.Theta.Geometric.SchemeFrameTransitions
import OAI.RepresentationTheory.Theta.Geometric.SchemeSectionNaturality

/-! # Scheme Frame Pullback -/

namespace OAI.RepresentationTheory.Theta.Geometric.SchemeFramePullback.SchemeFrames

noncomputable section

/-! Local pullback-frame transitions evaluate to the original transition
functions composed with the actual map of complex points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.RepresentationTheory.Theta.Geometric.SchemeSectionNaturality.SchemeSectionEvaluation

variable {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : Y ⟶ X)
    {M : X.left.Modules}

theorem pullbackFrame_analytic_mem (s : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame M) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) :
    p ∈ SchemeFrameTransitions.SchemeFrames.frameAnalyticOpen Y (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.PullbackFrames.pullbackLocalFrame f.left M s) ↔
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p ∈ SchemeFrameTransitions.SchemeFrames.frameAnalyticOpen X s := Iff.rfl

theorem pullbackFrame_pointTransition (s t : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame M)
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
    (hs : p ∈ SchemeFrameTransitions.SchemeFrames.frameAnalyticOpen Y (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.PullbackFrames.pullbackLocalFrame f.left M s))
    (ht : p ∈ SchemeFrameTransitions.SchemeFrames.frameAnalyticOpen Y (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.PullbackFrames.pullbackLocalFrame f.left M t)) :
    SchemeFrameTransitions.SchemeFrames.framePointTransition Y (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.PullbackFrames.pullbackLocalFrame f.left M s) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.PullbackFrames.pullbackLocalFrame f.left M t) p hs ht =
      SchemeFrameTransitions.SchemeFrames.framePointTransition X s t (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) hs ht := by
  let U := s.domain ⊓ t.domain
  let W := f.left ⁻¹ᵁ U
  let q : SchemeSectionNaturality.SchemeSectionEvaluation.analyticOpen Y W := ⟨p, hs, ht⟩
  have h := congrArg (fun u : Γ(Y.left, W)ˣ => SchemeSectionNaturality.SchemeSectionEvaluation.sectionEvaluationOn Y W (u : Γ(Y.left, W)) q)
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.FrameCoordinates.pullbackLocalFrame_transition f.left M s t U inf_le_left inf_le_right)
  change SchemeSectionNaturality.SchemeSectionEvaluation.sectionEvaluationOn Y W
    (f.left.app U (s.transition t U inf_le_left inf_le_right : Γ(X.left, U))) q = _ at h
  have he := SchemeSectionNaturality.SchemeSectionEvaluation.sectionEvaluationOn_appLE f U W le_rfl
    (s.transition t U inf_le_left inf_le_right : Γ(X.left, U)) q
  have he' := (congrArg (fun a : Γ(X.left, U) ⟶ Γ(Y.left, W) =>
    SchemeSectionNaturality.SchemeSectionEvaluation.sectionEvaluationOn Y W (a (s.transition t U inf_le_left inf_le_right : Γ(X.left, U))) q)
    (Scheme.Hom.appLE_eq_app f.left (U := U))).symm.trans he
  have htarg := SchemeFrameTransitions.SchemeFrames.framePointTransition_restrict Y
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.PullbackFrames.pullbackLocalFrame f.left M s) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.PullbackFrames.pullbackLocalFrame f.left M t) W
    (fun _ hx => hx.1) (fun _ hx => hx.2) q
  have hsource := SchemeFrameTransitions.SchemeFrames.framePointTransition_restrict X s t U inf_le_left inf_le_right
    (SchemeSectionNaturality.SchemeSectionEvaluation.analyticOpenMap f U W le_rfl q)
  exact htarg.trans (h.symm.trans (he'.trans hsource.symm))

end

end OAI.RepresentationTheory.Theta.Geometric.SchemeFramePullback.SchemeFrames
