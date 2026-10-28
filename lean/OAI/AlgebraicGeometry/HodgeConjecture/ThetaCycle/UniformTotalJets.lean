import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ParameterHalfDet
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CompactFiber
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PartialSmoothJets

/-! # Uniform Total Jets -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.UniformTotalJets.CM

noncomputable section

/-! ThetaCycle: convergence of every real ball derivative of every completed
Jacobi jet, uniformly on each compact ball chart, with one fixed finite input. -/

open scoped Classical _root_.Matrix _root_.Topology ContDiff _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM Filter

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase)
  (Φ : RepresentationTheory.Theta.DerivativeFactorizationDefinitions.Input (PeriodTotal.CM.TotalPositions K D.places)) (a : ℕ)

def parameterJacobiJet (q : ParameterHalfDet.CM.ParameterPoint K D) :
    ContinuousMultilinearMap ℂ (fun _ : Fin a => PeriodTotal.CM.TotalPositions K D.places → ℂ) ℂ :=
  TotalJetRegularity.CM.finiteCompletedJet Φ a (ParameterHalfDet.CM.parameterPeriodChart K D q)

theorem parameter_jacobi_jet_smoothAt_original (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ D.ball.domain) :
    ContDiffAt ℝ ∞ (parameterJacobiJet K D Φ a) (ApproximationSequence.CM.oldCompactPeriods K D, z) := by
  have hc := (ParameterHalfDet.CM.parameter_period_chart_smooth K D).contDiffAt
    ((ParameterHalfDet.CM.parameter_graph_domain_open K D).mem_nhds (ParameterHalfDet.CM.parameter_graph_domain_original K D z hz))
  have hj : ContDiffAt ℝ ∞ (TotalJetRegularity.CM.finiteCompletedJet Φ a)
      (ParameterHalfDet.CM.parameterPeriodChart K D (ApproximationSequence.CM.oldCompactPeriods K D, z)) := by
    rw [ParameterHalfDet.CM.parameter_period_chart_original K D z hz]
    exact (TotalJetRegularity.CM.finite_completed_jet_contDiffAt Φ a (PeriodLimit.CM.initialTotalPeriod K D z)).of_le (by simp)
  exact hj.comp _ hc

theorem parameter_ball_jacobi_continuousAt_original (m : ℕ)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ D.ball.domain) :
    ContinuousAt (fun q : ParameterHalfDet.CM.ParameterPoint K D =>
      iteratedFDeriv ℝ m (fun w => parameterJacobiJet K D Φ a (q.1, w)) q.2)
      (ApproximationSequence.CM.oldCompactPeriods K D, z) :=
  (PartialSmoothJets.CM.partial_iteratedFDeriv_smoothAt (𝕜 := ℝ)
    (f := fun p w => parameterJacobiJet K D Φ a (p, w))
    (parameter_jacobi_jet_smoothAt_original K D Φ a z hz) m).continuousAt

theorem parameter_jacobi_jet_approximation {ε : ℝ}
    (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε) (z : HeckeCycles.GeometricSource.CM.BallChart)
    (hq : (ApproximationSequence.CM.newCompactPeriods K D A, z) ∈ ParameterHalfDet.CM.parameterGraphDomain K D) :
    parameterJacobiJet K D Φ a (ApproximationSequence.CM.newCompactPeriods K D A, z) =
      iteratedFDeriv ℂ a (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed Φ (MovingTotalPeriod.CM.approximationTotalPeriod K D A z)) 0 := by
  unfold parameterJacobiJet TotalJetRegularity.CM.finiteCompletedJet
  rw [ParameterHalfDet.CM.parameter_period_chart_approximation K D A z hq, TotalJetRegularity.CM.finite_completed_theta_eq]

theorem parameter_jacobi_jet_original (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ D.ball.domain) :
    parameterJacobiJet K D Φ a (ApproximationSequence.CM.oldCompactPeriods K D, z) =
      iteratedFDeriv ℂ a (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed Φ (PeriodLimit.CM.initialTotalPeriod K D z)) 0 := by
  unfold parameterJacobiJet TotalJetRegularity.CM.finiteCompletedJet
  rw [ParameterHalfDet.CM.parameter_period_chart_original K D z hz, TotalJetRegularity.CM.finite_completed_theta_eq]

theorem parameter_ball_jacobi_approximation (m : ℕ) {ε : ℝ}
    (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε) (z : HeckeCycles.GeometricSource.CM.BallChart)
    (hq : (ApproximationSequence.CM.newCompactPeriods K D A, z) ∈ ParameterHalfDet.CM.parameterGraphDomain K D) :
    iteratedFDeriv ℝ m (fun w => parameterJacobiJet K D Φ a (ApproximationSequence.CM.newCompactPeriods K D A, w)) z =
      iteratedFDeriv ℝ m (fun w => iteratedFDeriv ℂ a
        (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed Φ (MovingTotalPeriod.CM.approximationTotalPeriod K D A w)) 0) z := by
  have hs : IsOpen ((fun w : HeckeCycles.GeometricSource.CM.BallChart => (ApproximationSequence.CM.newCompactPeriods K D A, w)) ⁻¹' ParameterHalfDet.CM.parameterGraphDomain K D) :=
    (ParameterHalfDet.CM.parameter_graph_domain_open K D).preimage (continuous_const.prodMk continuous_id)
  have he : (fun w => parameterJacobiJet K D Φ a (ApproximationSequence.CM.newCompactPeriods K D A, w)) =ᶠ[𝓝 z]
      (fun w => iteratedFDeriv ℂ a (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed Φ (MovingTotalPeriod.CM.approximationTotalPeriod K D A w)) 0) := by
    filter_upwards [hs.mem_nhds hq] with w hw
    exact parameter_jacobi_jet_approximation K D Φ a A w hw
  exact (he.iteratedFDeriv ℝ m).self_of_nhds

theorem parameter_ball_jacobi_original (m : ℕ) (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ D.ball.domain) :
    iteratedFDeriv ℝ m (fun w => parameterJacobiJet K D Φ a (ApproximationSequence.CM.oldCompactPeriods K D, w)) z =
      iteratedFDeriv ℝ m (fun w => iteratedFDeriv ℂ a
        (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed Φ (PeriodLimit.CM.initialTotalPeriod K D w)) 0) z := by
  have he : (fun w => parameterJacobiJet K D Φ a (ApproximationSequence.CM.oldCompactPeriods K D, w)) =ᶠ[𝓝 z]
      (fun w => iteratedFDeriv ℂ a (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed Φ (PeriodLimit.CM.initialTotalPeriod K D w)) 0) := by
    filter_upwards [D.ball.domain_isOpen.mem_nhds hz] with w hw
    exact parameter_jacobi_jet_original K D Φ a w hw
  exact (he.iteratedFDeriv ℝ m).self_of_nhds

/-- This is genuine C-infinity convergence of the unprojected total Jacobi
jets on compact ball charts, derived from the rational arithmetic approximation. -/
theorem approximation_total_jets_uniform_derivatives (m : ℕ)
    (S : Set HeckeCycles.GeometricSource.CM.BallChart) (hS : IsCompact S) (hSB : S ⊆ D.ball.domain) :
    TendstoUniformlyOn
      (fun n z => iteratedFDeriv ℝ m (fun w => iteratedFDeriv ℂ a
        (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed Φ (MovingTotalPeriod.CM.approximationTotalPeriod K D (ApproximationSequence.CM.approximationSequence K D n) w)) 0) z)
      (fun z => iteratedFDeriv ℝ m (fun w => iteratedFDeriv ℂ a
        (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed Φ (PeriodLimit.CM.initialTotalPeriod K D w)) 0) z) atTop S := by
  have hlim := CompactFiber.CM.compact_fiber_uniform_limit
    (fun n => ApproximationSequence.CM.newCompactPeriods K D (ApproximationSequence.CM.approximationSequence K D n)) (ApproximationSequence.CM.oldCompactPeriods K D)
    (ApproximationSequence.CM.sequence_compact_periods_tendsto K D)
    (fun p z => iteratedFDeriv ℝ m (fun w => parameterJacobiJet K D Φ a (p, w)) z) S hS
    (fun z hz => parameter_ball_jacobi_continuousAt_original K D Φ a m z (hSB hz))
  have htube := CompactFiber.CM.eventually_compact_fiber_mem
    (fun n => ApproximationSequence.CM.newCompactPeriods K D (ApproximationSequence.CM.approximationSequence K D n)) (ApproximationSequence.CM.oldCompactPeriods K D)
    (ApproximationSequence.CM.sequence_compact_periods_tendsto K D) S hS (ParameterHalfDet.CM.parameterGraphDomain K D)
    (ParameterHalfDet.CM.parameter_graph_domain_open K D) (fun z hz => ParameterHalfDet.CM.parameter_graph_domain_original K D z (hSB hz))
  rw [Metric.tendstoUniformlyOn_iff] at hlim ⊢
  intro ε hε
  filter_upwards [hlim ε hε, htube] with n hn htn
  intro z hz
  have h := hn z hz
  rw [parameter_ball_jacobi_original K D Φ a m z (hSB hz),
    parameter_ball_jacobi_approximation K D Φ a m (ApproximationSequence.CM.approximationSequence K D n) z (htn z hz)] at h
  exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.UniformTotalJets.CM
