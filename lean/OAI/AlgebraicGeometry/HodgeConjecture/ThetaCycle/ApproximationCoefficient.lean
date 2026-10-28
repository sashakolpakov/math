import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ProjectedCoefficient
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TransportedGraphFrame

/-! # Approximation Coefficient -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ApproximationCoefficient.CM

noncomputable section

/-! ThetaCycle: compact C-infinity convergence for the literal moving-period
theta coefficient, including its graph slots and normalized half-determinant. -/

open scoped Classical _root_.Matrix _root_.Topology ContDiff _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM Filter

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase)
  (Φ : RepresentationTheory.Theta.DerivativeFactorizationDefinitions.Input (PeriodTotal.CM.TotalPositions K D.places))

def approximationProjectedCoefficient {ε : ℝ}
    (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε) (z : HeckeCycles.GeometricSource.CM.BallChart) : ℂ :=
  RepresentationTheory.Theta.Kernel.Calculus.doubleAlt (fun a b => ParameterHalfDet.CM.parameterHalfDet K D (ApproximationSequence.CM.newCompactPeriods K D A, z) *
    iteratedFDeriv ℂ 2 (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed Φ (MovingTotalPeriod.CM.approximationTotalPeriod K D A z)) 0
      ![TotalGraphSlots.CM.totalGraphSlot K (fun i => (D.initialPeriods i).coordinates) (MovingTotalPeriod.CM.approximationTotalPeriod K D A z).matrix a,
        TotalGraphSlots.CM.totalGraphSlot K (fun i => (D.initialPeriods i).coordinates) (MovingTotalPeriod.CM.approximationTotalPeriod K D A z).matrix b])

theorem parameter_projected_coefficient_approximation {ε : ℝ}
    (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε) (z : HeckeCycles.GeometricSource.CM.BallChart)
    (hq : (ApproximationSequence.CM.newCompactPeriods K D A, z) ∈ ParameterHalfDet.CM.parameterGraphDomain K D) :
    ProjectedCoefficient.CM.parameterProjectedCoefficient K D Φ (ApproximationSequence.CM.newCompactPeriods K D A, z) =
      approximationProjectedCoefficient K D Φ A z := by
  unfold ProjectedCoefficient.CM.parameterProjectedCoefficient ProjectedCoefficient.CM.parameterProjectedTensor ProjectedCoefficient.CM.parameterTotalSlot approximationProjectedCoefficient
  rw [UniformTotalJets.CM.parameter_jacobi_jet_approximation K D Φ 2 A z hq,
    ParameterHalfDet.CM.parameter_period_chart_approximation K D A z hq]

theorem parameter_projected_ball_derivatives_approximation (m : ℕ) {ε : ℝ}
    (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε) (z : HeckeCycles.GeometricSource.CM.BallChart)
    (hq : (ApproximationSequence.CM.newCompactPeriods K D A, z) ∈ ParameterHalfDet.CM.parameterGraphDomain K D) :
    iteratedFDeriv ℝ m (fun w => ProjectedCoefficient.CM.parameterProjectedCoefficient K D Φ (ApproximationSequence.CM.newCompactPeriods K D A, w)) z =
      iteratedFDeriv ℝ m (approximationProjectedCoefficient K D Φ A) z := by
  have hs : IsOpen ((fun w : HeckeCycles.GeometricSource.CM.BallChart => (ApproximationSequence.CM.newCompactPeriods K D A, w)) ⁻¹' ParameterHalfDet.CM.parameterGraphDomain K D) :=
    (ParameterHalfDet.CM.parameter_graph_domain_open K D).preimage (continuous_const.prodMk continuous_id)
  have he : (fun w => ProjectedCoefficient.CM.parameterProjectedCoefficient K D Φ (ApproximationSequence.CM.newCompactPeriods K D A, w)) =ᶠ[𝓝 z]
      approximationProjectedCoefficient K D Φ A := by
    filter_upwards [hs.mem_nhds hq] with w hw
    exact parameter_projected_coefficient_approximation K D Φ A w hw
  exact (he.iteratedFDeriv ℝ m).self_of_nhds

theorem approximation_projected_coefficient_uniform_derivatives (m : ℕ)
    (S : Set HeckeCycles.GeometricSource.CM.BallChart) (hS : IsCompact S) (hSB : S ⊆ D.ball.domain) :
    TendstoUniformlyOn
      (fun n z => iteratedFDeriv ℝ m (approximationProjectedCoefficient K D Φ (ApproximationSequence.CM.approximationSequence K D n)) z)
      (fun z => iteratedFDeriv ℝ m
        (InitialTensor.CM.splitThetaTopCoefficient K (D.initialPeriods 0) (D.initialPeriods 1) Φ) z) atTop S := by
  have hlim := ProjectedCoefficient.CM.parameter_projected_coefficient_uniform_derivatives K D Φ m S hS hSB
  have htube := CompactFiber.CM.eventually_compact_fiber_mem
    (fun n => ApproximationSequence.CM.newCompactPeriods K D (ApproximationSequence.CM.approximationSequence K D n)) (ApproximationSequence.CM.oldCompactPeriods K D)
    (ApproximationSequence.CM.sequence_compact_periods_tendsto K D) S hS (ParameterHalfDet.CM.parameterGraphDomain K D)
    (ParameterHalfDet.CM.parameter_graph_domain_open K D) (fun z hz => ParameterHalfDet.CM.parameter_graph_domain_original K D z (hSB hz))
  rw [Metric.tendstoUniformlyOn_iff] at hlim ⊢
  intro ε hε
  filter_upwards [hlim ε hε, htube] with n hn htn
  intro z hz
  rw [← parameter_projected_ball_derivatives_approximation K D Φ m
    (ApproximationSequence.CM.approximationSequence K D n) z (htn z hz)]
  exact hn z hz

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ApproximationCoefficient.CM
