import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.UniformTotalJets
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TotalGraphSlots
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ParameterHalfDet
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BilinearEvaluation

/-! # Projected Coefficient -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ProjectedCoefficient.CM

noncomputable section

/-! ThetaCycle: the actual graph-projected total theta Hessian in one
normalized local half-determinant frame, retaining the same finite input. -/

open scoped Classical _root_.Matrix _root_.Topology ContDiff _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM Filter

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase)
  (Φ : RepresentationTheory.Theta.DerivativeFactorizationDefinitions.Input (PeriodTotal.CM.TotalPositions K D.places))

def parameterTotalSlot (q : ParameterHalfDet.CM.ParameterPoint K D) (a : Fin 2 × Fin 2) :
    PeriodTotal.CM.TotalPositions K D.places → ℂ :=
  TotalGraphSlots.CM.totalGraphSlot K (fun i => (D.initialPeriods i).coordinates) (ParameterHalfDet.CM.parameterPeriodChart K D q) a

def parameterProjectedTensor (q : ParameterHalfDet.CM.ParameterPoint K D) : RepresentationTheory.Theta.Kernel.Calculus.TensorCoordinates := fun a b =>
  ParameterHalfDet.CM.parameterHalfDet K D q * UniformTotalJets.CM.parameterJacobiJet K D Φ 2 q
    ![parameterTotalSlot K D q a, parameterTotalSlot K D q b]

def parameterProjectedCoefficient (q : ParameterHalfDet.CM.ParameterPoint K D) : ℂ :=
  RepresentationTheory.Theta.Kernel.Calculus.doubleAlt (parameterProjectedTensor K D Φ q)

theorem parameter_total_slot_smoothAt_original (a : Fin 2 × Fin 2)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ D.ball.domain) :
    ContDiffAt ℝ ∞ (fun q => parameterTotalSlot K D q a) (ApproximationSequence.CM.oldCompactPeriods K D, z) := by
  have h := TotalGraphSlots.CM.total_graph_slot_holomorphic K (fun i => (D.initialPeriods i).coordinates)
    (ParameterHalfDet.CM.parameterPeriodChart K D) (ParameterHalfDet.CM.parameter_period_chart_holomorphic K D) a
  exact ((Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF.Constructions.HolomorphicDerivative.contDiffOn_infty_of_differentiableOn
    (ParameterHalfDet.CM.parameter_graph_domain_open K D) h).restrict_scalars ℝ).contDiffAt
      ((ParameterHalfDet.CM.parameter_graph_domain_open K D).mem_nhds (ParameterHalfDet.CM.parameter_graph_domain_original K D z hz))

theorem parameter_projected_tensor_smoothAt_original (a b : Fin 2 × Fin 2)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ D.ball.domain) :
    ContDiffAt ℝ ∞ (fun q => parameterProjectedTensor K D Φ q a b) (ApproximationSequence.CM.oldCompactPeriods K D, z) := by
  have hj := (UniformTotalJets.CM.parameter_jacobi_jet_smoothAt_original K D Φ 2 z hz).continuousLinearMap_comp
    (ContinuousMultilinearMap.restrictScalarsₗᵢ ℝ).toContinuousLinearMap
  have he := BilinearEvaluation.CM.bilinear_evaluation_smoothAt hj
    (parameter_total_slot_smoothAt_original K D a z hz)
    (parameter_total_slot_smoothAt_original K D b z hz)
  have hh := (ParameterHalfDet.CM.parameter_half_det_smooth K D).contDiffAt
    ((ParameterHalfDet.CM.parameter_half_det_domain_open K D).mem_nhds (ParameterHalfDet.CM.parameter_half_det_domain_original K D z hz))
  exact hh.mul he

theorem parameter_projected_coefficient_smoothAt_original
    (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ D.ball.domain) :
    ContDiffAt ℝ ∞ (parameterProjectedCoefficient K D Φ) (ApproximationSequence.CM.oldCompactPeriods K D, z) := by
  have h := parameter_projected_tensor_smoothAt_original K D Φ
  exact ((((h (0, 0) (1, 1) z hz).sub (h (1, 0) (0, 1) z hz)).sub
    (h (0, 1) (1, 0) z hz)).add (h (1, 1) (0, 0) z hz)).div_const 2

theorem parameter_total_slot_original (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ D.ball.domain)
    (a : Fin 2 × Fin 2) :
    parameterTotalSlot K D (ApproximationSequence.CM.oldCompactPeriods K D, z) a =
      InitialTensor.CM.splitThetaSlot K (D.initialPeriods 0) (D.initialPeriods 1) z a := by
  unfold parameterTotalSlot
  rw [ParameterHalfDet.CM.parameter_period_chart_original K D z hz]
  have hc : (fun i => (D.initialPeriods i).coordinates) =
      ![(D.initialPeriods 0).coordinates, (D.initialPeriods 1).coordinates] := by
    funext i
    fin_cases i <;> rfl
  rw [hc]
  exact TotalGraphSlots.CM.total_graph_slot_block K (D.initialPeriods 0) (D.initialPeriods 1) z a

theorem parameter_projected_coefficient_original (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ D.ball.domain) :
    parameterProjectedCoefficient K D Φ (ApproximationSequence.CM.oldCompactPeriods K D, z) =
      InitialTensor.CM.splitThetaTopCoefficient K (D.initialPeriods 0) (D.initialPeriods 1) Φ z := by
  unfold parameterProjectedCoefficient parameterProjectedTensor InitialTensor.CM.splitThetaTopCoefficient InitialTensor.CM.splitThetaTensor
  simp only [ParameterHalfDet.CM.parameter_half_det_original K D z hz, UniformTotalJets.CM.parameter_jacobi_jet_original K D Φ 2 z hz,
    parameter_total_slot_original K D z hz]
  rfl

theorem parameter_projected_coefficient_uniform_derivatives (m : ℕ)
    (S : Set HeckeCycles.GeometricSource.CM.BallChart) (hS : IsCompact S) (hSB : S ⊆ D.ball.domain) :
    TendstoUniformlyOn
      (fun n z => iteratedFDeriv ℝ m (fun w => parameterProjectedCoefficient K D Φ
        (ApproximationSequence.CM.newCompactPeriods K D (ApproximationSequence.CM.approximationSequence K D n), w)) z)
      (fun z => iteratedFDeriv ℝ m (fun w =>
        InitialTensor.CM.splitThetaTopCoefficient K (D.initialPeriods 0) (D.initialPeriods 1) Φ w) z) atTop S := by
  have hlim := CompactFiber.CM.compact_fiber_uniform_limit
    (fun n => ApproximationSequence.CM.newCompactPeriods K D (ApproximationSequence.CM.approximationSequence K D n)) (ApproximationSequence.CM.oldCompactPeriods K D)
    (ApproximationSequence.CM.sequence_compact_periods_tendsto K D)
    (fun p z => iteratedFDeriv ℝ m (fun w => parameterProjectedCoefficient K D Φ (p, w)) z) S hS
    (fun z hz => (PartialSmoothJets.CM.partial_iteratedFDeriv_smoothAt (𝕜 := ℝ)
      (f := fun p w => parameterProjectedCoefficient K D Φ (p, w))
      (parameter_projected_coefficient_smoothAt_original K D Φ z (hSB hz)) m).continuousAt)
  rw [Metric.tendstoUniformlyOn_iff] at hlim ⊢
  intro ε hε
  filter_upwards [hlim ε hε] with n hn
  intro z hz
  have he : (fun w => parameterProjectedCoefficient K D Φ (ApproximationSequence.CM.oldCompactPeriods K D, w)) =ᶠ[𝓝 z]
      (fun w => InitialTensor.CM.splitThetaTopCoefficient K (D.initialPeriods 0) (D.initialPeriods 1) Φ w) := by
    filter_upwards [D.ball.domain_isOpen.mem_nhds (hSB hz)] with w hw
    exact parameter_projected_coefficient_original K D Φ w hw
  rw [← (he.iteratedFDeriv ℝ m).self_of_nhds]
  exact hn z hz

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ProjectedCoefficient.CM
