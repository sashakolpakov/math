import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoordinateProjector
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TotalJetRegularity

/-! # Period Limit -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PeriodLimit.CM

noncomputable section

/-! ThetaCycle: the concrete rational approximations converge in the original
Siegel coordinates, with the same total finite input in every Jacobi jet. -/

open scoped Classical _root_.Matrix _root_.Topology ContDiff _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM Filter

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase)

def initialTotalPeriod (z : HeckeCycles.GeometricSource.CM.BallChart) : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (PeriodTotal.CM.TotalPositions K D.places) :=
  BlockPeriod.CM.blockPeriod ((D.initialPeriods 0).period z) ((D.initialPeriods 1).period z)

theorem approximation_total_period_tendsto (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ D.ball.domain) :
    Tendsto (fun n => (MovingTotalPeriod.CM.approximationTotalPeriod K D (ApproximationSequence.CM.approximationSequence K D n) z).matrix)
      atTop (𝓝 (initialTotalPeriod K D z).matrix) := by
  let C := fun i => (D.initialPeriods i).coordinates
  let P := fun n => TotalProjector.CM.approximationProjector K D (ApproximationSequence.CM.approximationSequence K D n) z
  let P₀ := TotalProjector.CM.totalSourceProjector K D.ball D.places (FourSplittings.CM.initialThetaSigns K v) z
  apply ProjectorCharts.CM.period_matrices_tendsto_of_projectors
    (fun n => CoordinateProjector.CM.coordinateProjector K C (P n))
    (fun n => (MovingTotalPeriod.CM.approximationTotalPeriod K D (ApproximationSequence.CM.approximationSequence K D n) z).matrix)
    (CoordinateProjector.CM.coordinateProjector K C P₀) (initialTotalPeriod K D z).matrix
  · exact CoordinateProjector.CM.coordinate_projector_graph_fixed K C P₀ (initialTotalPeriod K D z)
      (TotalProjector.CM.total_source_projector_graph_fixed K D.initialPeriods z hz)
  · exact CoordinateProjector.CM.coordinate_projectors_tendsto K C P P₀ (ProjectorParameters.CM.approximation_projectors_tendsto K D z)
  · intro n
    exact CoordinateProjector.CM.coordinate_projector_graph_image K C (P n) (initialTotalPeriod K D z).matrix
      (MovingTotalPeriod.CM.approximationTotalPeriod K D (ApproximationSequence.CM.approximationSequence K D n) z)
      (TotalProjector.CM.approximation_projector_graph_image K D (ApproximationSequence.CM.approximationSequence K D n) z hz)

/-- Every completed Jacobi derivative has the correct pointwise limit for
one fixed genuine total finite Schwartz input. -/
theorem approximation_total_jets_tendsto
    (Φ : RepresentationTheory.Theta.DerivativeFactorizationDefinitions.Input (PeriodTotal.CM.TotalPositions K D.places)) (a : ℕ)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ D.ball.domain) :
    Tendsto (fun n => iteratedFDeriv ℂ a
      (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed Φ (MovingTotalPeriod.CM.approximationTotalPeriod K D (ApproximationSequence.CM.approximationSequence K D n) z)) 0)
      atTop (𝓝 (iteratedFDeriv ℂ a (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed Φ (initialTotalPeriod K D z)) 0)) := by
  have h := (TotalJetRegularity.CM.finite_completed_jet_contDiffAt Φ a (initialTotalPeriod K D z)).continuousAt.tendsto.comp
    (approximation_total_period_tendsto K D z hz)
  simpa only [Function.comp_def, TotalJetRegularity.CM.finiteCompletedJet, TotalJetRegularity.CM.finite_completed_theta_eq] using h

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PeriodLimit.CM
