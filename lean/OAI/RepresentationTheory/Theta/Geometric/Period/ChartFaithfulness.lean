import OAI.RepresentationTheory.Theta.Geometric.Rational.ThetaPullback

/-! # Chart Faithfulness -/

namespace OAI.RepresentationTheory.Theta.Geometric.Period.ChartFaithfulness

noncomputable section

/-! Preferred ball-chart evaluations determine an actual smooth one-form. -/

set_option backward.isDefEq.respectTransparency false

theorem smoothForm_eq_of_periodChartEvaluation (Ω : TopologicalSpace.Opens LinearTheta.BallCoordinates)
    (form other : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm LinearTheta.BallCoordinates Ω 1)
    (h : ∀ (x : Ω) (u : LinearTheta.BallCoordinates),
      Projective.FormOnDomain.periodChartEvaluation Ω x u form = Projective.FormOnDomain.periodChartEvaluation Ω x u other) : form = other := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  ext v
  have he := (Rational.ThetaPullback.periodChartEvaluation_apply Ω x (v 0) form).symm.trans
    ((h x (v 0)).trans (Rational.ThetaPullback.periodChartEvaluation_apply Ω x (v 0) other))
  have hv : (fun _ : Fin 1 => v 0) = v := funext (fun i => congrArg v (Subsingleton.elim 0 i))
  simpa only [hv] using he

end

end OAI.RepresentationTheory.Theta.Geometric.Period.ChartFaithfulness
