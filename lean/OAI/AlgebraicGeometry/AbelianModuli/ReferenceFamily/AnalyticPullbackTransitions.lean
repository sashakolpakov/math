import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.FrameCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AnalyticFrameTransitions
import OAI.AlgebraicGeometry.DivisorClass.Chern.AnalyticCover

/-! # Analytic Pullback Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AnalyticPullbackTransitions

noncomputable section

/-! Local pullback-frame transitions evaluate to the original transition
functions composed with the actual map of complex points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : Y.toOver ⟶ X.toOver)
    {M : X.carrier.Modules}

theorem pullbackFrame_analytic_mem (s : LineFrameAtlas.LocalLineFrame M) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y.toOver) :
    p ∈ AnalyticFrameTransitions.frameAnalyticOpen Y (Local.PullbackFrames.pullbackLocalFrame f.left M s) ↔
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p ∈ AnalyticFrameTransitions.frameAnalyticOpen X s := Iff.rfl

theorem pullbackFrame_pointTransition (s t : LineFrameAtlas.LocalLineFrame M)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y.toOver)
    (hs : p ∈ AnalyticFrameTransitions.frameAnalyticOpen Y (Local.PullbackFrames.pullbackLocalFrame f.left M s))
    (ht : p ∈ AnalyticFrameTransitions.frameAnalyticOpen Y (Local.PullbackFrames.pullbackLocalFrame f.left M t)) :
    AnalyticFrameTransitions.framePointTransition Y (Local.PullbackFrames.pullbackLocalFrame f.left M s) (Local.PullbackFrames.pullbackLocalFrame f.left M t) p hs ht =
      AnalyticFrameTransitions.framePointTransition X s t (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) hs ht := by
  let U := s.domain ⊓ t.domain
  let W := f.left ⁻¹ᵁ U
  let q : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen Y W := ⟨p, hs, ht⟩
  have h := congrArg (fun u : Γ(Y.carrier, W)ˣ => DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn Y W (u : Γ(Y.carrier, W)) q)
    (Pullback.FrameCoordinates.pullbackLocalFrame_transition f.left M s t U inf_le_left inf_le_right)
  change DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn Y W
    (f.left.app U (s.transition t U inf_le_left inf_le_right : Γ(X.carrier, U))) q = _ at h
  have he := DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_appLE f U W le_rfl
    (s.transition t U inf_le_left inf_le_right : Γ(X.carrier, U)) q
  have he' := (congrArg (fun a : Γ(X.carrier, U) ⟶ Γ(Y.carrier, W) =>
    DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn Y W (a (s.transition t U inf_le_left inf_le_right : Γ(X.carrier, U))) q)
    (Scheme.Hom.appLE_eq_app f.left (U := U))).symm.trans he
  have htarg := AnalyticFrameTransitions.framePointTransition_restrict Y
    (Local.PullbackFrames.pullbackLocalFrame f.left M s) (Local.PullbackFrames.pullbackLocalFrame f.left M t) W
    (fun _ hx => hx.1) (fun _ hx => hx.2) q
  have hsource := AnalyticFrameTransitions.framePointTransition_restrict X s t U inf_le_left inf_le_right
    (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpenMap f U W le_rfl q)
  exact htarg.trans (h.symm.trans (he'.trans hsource.symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AnalyticPullbackTransitions
