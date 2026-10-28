import OAI.RepresentationTheory.Theta.Geometric.ConsecutiveGauge

/-! # Gauge Derivative Holomorphic -/

namespace OAI.RepresentationTheory.Theta.Geometric.GaugeDerivativeHolomorphic.CM.Torus.AutomorphicTheta

noncomputable section

/-! Directional derivatives of the actual consecutive theta gauges are
holomorphic on their original nonzero-coordinate domains. -/

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}

theorem consecutiveGauge_directionalDerivative_differentiableAt (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)
    (i : Fin (F.projectiveDimension + 1)) (j : Fin (G.projectiveDimension + 1))
    (z a : Φ.space) (hi : F.coordinate i z ≠ 0) :
    DifferentiableAt ℂ (fun w => fderiv ℂ (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i j) w a) z := by
  let U := {w : Φ.space | F.coordinate i w ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun (F.coordinate i).continuous continuous_const
  have hg : DifferentiableOn ℂ (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i j) U :=
    fun w hw => (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_differentiableAt F G i j w hw).differentiableWithinAt
  exact Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.holomorphic_differentiable_fderiv_apply hU hg hi a

end

end OAI.RepresentationTheory.Theta.Geometric.GaugeDerivativeHolomorphic.CM.Torus.AutomorphicTheta
