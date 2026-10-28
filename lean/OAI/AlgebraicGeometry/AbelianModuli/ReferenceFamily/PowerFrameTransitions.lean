import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PowerFrameCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AnalyticFrameTransitions

/-! # Power Frame Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The actual transition units of a tensor power are powers of the
original transition units, on algebraic and analytic overlaps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme.{0}} {M : X.Modules}

def LineFrameAtlas.LocalLineFrame.power (s : LineFrameAtlas.LocalLineFrame M) (n : ℕ) : LineFrameAtlas.LocalLineFrame (HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule M n) where
  domain := s.domain
  frame := PowerFrameCoordinates.powerFrameOnDomain M n s.domain s.frame

theorem LineFrameAtlas.LocalLineFrame.power_transition (s t : LineFrameAtlas.LocalLineFrame M) (n : ℕ)
    (W : X.Opens) (hs : W ≤ s.domain) (ht : W ≤ t.domain) :
    (s.power n).transition (t.power n) W hs ht = s.transition t W hs ht ^ n :=
  PowerFrameCoordinates.frameTransitionUnit_multilinear n ((HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear M n).app W) _ _ _ _
    (PowerFrameCoordinates.powerFrameOnOpen_apply M n s.domain s.frame W hs)
    (PowerFrameCoordinates.powerFrameOnOpen_apply M n t.domain t.frame W ht)

theorem PowerFrameTransitions.sectionEvaluationOn_pow (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W : P.carrier.Opens)
    (a : Γ(P.carrier, W)) (n : ℕ) (p : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen P W) :
    DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn P W (a ^ n) p = DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn P W a p ^ n := by
  change DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation ((DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openPointHomeomorph P W).symm p)
    (W.topIso.inv (a ^ n)) = _
  rw [map_pow, map_pow]
  rfl

theorem PowerFrameTransitions.powerFrame_pointTransition {P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} {L : P.carrier.Modules}
    (s t : LineFrameAtlas.LocalLineFrame L) (n : ℕ) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)
    (hs : p ∈ AnalyticFrameTransitions.frameAnalyticOpen P s) (ht : p ∈ AnalyticFrameTransitions.frameAnalyticOpen P t) :
    AnalyticFrameTransitions.framePointTransition P (s.power n) (t.power n) p hs ht =
      AnalyticFrameTransitions.framePointTransition P s t p hs ht ^ n := by
  let q : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen P (s.domain ⊓ t.domain) := ⟨p, hs, ht⟩
  have h := congrArg (fun u : Γ(P.carrier, s.domain ⊓ t.domain)ˣ =>
    DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn P (s.domain ⊓ t.domain) (u : Γ(P.carrier, s.domain ⊓ t.domain)) q)
      (s.power_transition t n (s.domain ⊓ t.domain) inf_le_left inf_le_right)
  change DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn P (s.domain ⊓ t.domain) _ q =
    DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn P (s.domain ⊓ t.domain)
      ((s.transition t (s.domain ⊓ t.domain) inf_le_left inf_le_right : Γ(P.carrier, _)) ^ n) q at h
  exact h.trans (PowerFrameTransitions.sectionEvaluationOn_pow P (s.domain ⊓ t.domain) _ n q)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
