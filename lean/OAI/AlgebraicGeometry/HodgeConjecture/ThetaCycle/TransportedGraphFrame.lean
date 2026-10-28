import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ParameterHalfDet

/-! # Transported Graph Frame -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TransportedGraphFrame.CM

noncomputable section

/-! ThetaCycle: the parameter-chart denominator is the actual change of
graph frame induced by the transported geometric projector. -/

open scoped Classical _root_.Matrix _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

theorem projector_graph_frame_substitution {I : Type*} [Fintype I] [DecidableEq I]
    (P : Matrix (Sum I I) (Sum I I) ℂ) (Z : Matrix I I ℂ)
    (hdet : (ProjectorCharts.CM.graphBottom P Z).det ≠ 0) (x : I → ℂ) :
    P *ᵥ Sum.elim (Z *ᵥ x) x =
      Sum.elim (ProjectorCharts.CM.projectorGraphChart P Z *ᵥ (ProjectorCharts.CM.graphBottom P Z *ᵥ x)) (ProjectorCharts.CM.graphBottom P Z *ᵥ x) := by
  have hm : ProjectorCharts.CM.projectorGraphChart P Z * ProjectorCharts.CM.graphBottom P Z = ProjectorCharts.CM.graphTop P Z :=
    Matrix.nonsing_inv_mul_cancel_right _ _ (isUnit_iff_ne_zero.mpr hdet)
  rw [Matrix.mulVec_mulVec, hm]
  funext i
  cases i with
  | inl i =>
    change (P *ᵥ Sum.elim (Z *ᵥ x) x) (Sum.inl i) =
      (CoordinateProjector.CM.matrixColumnProduct P (Matrix.fromRows Z 1) *ᵥ x) (Sum.inl i)
    rw [CoordinateProjector.CM.matrix_column_product_mulVec, Matrix.fromRows_mulVec, Matrix.one_mulVec]
  | inr i =>
    change (P *ᵥ Sum.elim (Z *ᵥ x) x) (Sum.inr i) =
      (CoordinateProjector.CM.matrixColumnProduct P (Matrix.fromRows Z 1) *ᵥ x) (Sum.inr i)
    rw [CoordinateProjector.CM.matrix_column_product_mulVec, Matrix.fromRows_mulVec, Matrix.one_mulVec]

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase)

theorem approximation_projector_reference_graph {ε : ℝ}
    (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε) (z : HeckeCycles.GeometricSource.CM.BallChart)
    (hq : (ApproximationSequence.CM.newCompactPeriods K D A, z) ∈ ParameterHalfDet.CM.parameterGraphDomain K D)
    (x : PeriodTotal.CM.TotalPositions K D.places → ℂ) :
    TotalProjector.CM.approximationProjector K D A z
        (TotalPeriodGraphs.CM.totalGraphInAmbient K (fun i => (D.initialPeriods i).coordinates) (PeriodLimit.CM.initialTotalPeriod K D z) x) =
      TotalPeriodGraphs.CM.totalGraphInAmbient K (fun i => (D.initialPeriods i).coordinates) (MovingTotalPeriod.CM.approximationTotalPeriod K D A z)
        (ParameterHalfDet.CM.parameterGraphBottom K D (ApproximationSequence.CM.newCompactPeriods K D A, z) *ᵥ x) := by
  apply (ComplexTransition.CM.totalComplexCoordinates K (fun i => (D.initialPeriods i).coordinates)).injective
  have hs := projector_graph_frame_substitution
    (ParameterProjectorAnalytic.CM.parameterCoordinateProjector K D (ApproximationSequence.CM.newCompactPeriods K D A) z)
    (PeriodLimit.CM.initialTotalPeriod K D z).matrix hq.2 x
  change _ = Sum.elim (ParameterHalfDet.CM.parameterPeriodChart K D (ApproximationSequence.CM.newCompactPeriods K D A, z) *ᵥ
    (ParameterHalfDet.CM.parameterGraphBottom K D (ApproximationSequence.CM.newCompactPeriods K D A, z) *ᵥ x))
    (ParameterHalfDet.CM.parameterGraphBottom K D (ApproximationSequence.CM.newCompactPeriods K D A, z) *ᵥ x) at hs
  rw [ParameterHalfDet.CM.parameter_period_chart_approximation K D A z hq,
    ParameterProjectorAnalytic.CM.parameter_coordinate_projector_approximation, CoordinateProjector.CM.coordinate_projector_mulVec] at hs
  rw [TotalPeriodGraphs.CM.total_graph_coordinates]
  exact hs

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TransportedGraphFrame.CM
