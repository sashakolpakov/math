import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ParameterProjectorAnalytic
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoordinateProjector
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PeriodLimit

/-! # Parameter Half Det -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ParameterHalfDet.CM

noncomputable section

section

/-! ThetaCycle: one holomorphic period chart around the original compact data,
with exact identification at every actual approximating splitting. -/

open scoped Classical _root_.Matrix _root_.Topology _root_.Matrix.Norms.Elementwise ContDiff
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM Filter

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase)

abbrev ParameterPoint := ParameterProjectorAnalytic.CM.CompactParameters K D.places × HeckeCycles.GeometricSource.CM.BallChart

def parameterBaseDomain : Set (ParameterPoint K D) := {q | q.2 ∈ D.ball.domain}

def parameterGraphBottom (q : ParameterPoint K D) :
    Matrix (PeriodTotal.CM.TotalPositions K D.places) (PeriodTotal.CM.TotalPositions K D.places) ℂ :=
  ProjectorCharts.CM.graphBottom (ParameterProjectorAnalytic.CM.parameterCoordinateProjector K D q.1 q.2) (PeriodLimit.CM.initialTotalPeriod K D q.2).matrix

def parameterGraphDomain : Set (ParameterPoint K D) :=
  {q | q.2 ∈ D.ball.domain ∧ (parameterGraphBottom K D q).det ≠ 0}

def parameterPeriodChart (q : ParameterPoint K D) :
    Matrix (PeriodTotal.CM.TotalPositions K D.places) (PeriodTotal.CM.TotalPositions K D.places) ℂ :=
  ProjectorCharts.CM.projectorGraphChart (ParameterProjectorAnalytic.CM.parameterCoordinateProjector K D q.1 q.2) (PeriodLimit.CM.initialTotalPeriod K D q.2).matrix

theorem initial_total_period_holomorphic :
    DifferentiableOn ℂ (fun z => (PeriodLimit.CM.initialTotalPeriod K D z).matrix) D.ball.domain :=
  MovingTotalPeriod.CM.block_period_holomorphic _ _ (D.initialPeriods 0).holomorphic (D.initialPeriods 1).holomorphic

theorem initial_parameter_period_holomorphic :
    DifferentiableOn ℂ (fun q : ParameterPoint K D => (PeriodLimit.CM.initialTotalPeriod K D q.2).matrix)
      (parameterBaseDomain K D) :=
  (initial_total_period_holomorphic K D).comp differentiableOn_snd (fun _ h => h)

theorem parameter_graph_bottom_holomorphic :
    DifferentiableOn ℂ (parameterGraphBottom K D) (parameterBaseDomain K D) :=
  (CoordinateProjector.CM.graph_blocks_holomorphic _ _ (ParameterProjectorAnalytic.CM.parameter_coordinate_projector_joint_holomorphic K D).differentiableOn
    (initial_parameter_period_holomorphic K D)).2

theorem parameter_graph_domain_open : IsOpen (parameterGraphDomain K D) := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  have hs : parameterBaseDomain K D ∈ 𝓝 q :=
    (D.ball.domain_isOpen.preimage continuous_snd).mem_nhds hq.1
  have hc : ContinuousAt (fun r => (parameterGraphBottom K D r).det) q :=
    ((MatrixCalculus.CM.matrix_determinant_holomorphic _ (parameter_graph_bottom_holomorphic K D)).differentiableAt hs).continuousAt
  exact inter_mem hs (hc.eventually_ne hq.2)

theorem parameter_graph_bottom_original (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ D.ball.domain) :
    parameterGraphBottom K D (ApproximationSequence.CM.oldCompactPeriods K D, z) = 1 := by
  unfold parameterGraphBottom
  rw [ParameterProjectorAnalytic.CM.parameter_coordinate_projector_original]
  exact (ProjectorCharts.CM.projector_chart_at_base _ _
    (CoordinateProjector.CM.coordinate_projector_graph_fixed K _ _ (PeriodLimit.CM.initialTotalPeriod K D z)
      (TotalProjector.CM.total_source_projector_graph_fixed K D.initialPeriods z hz))).2.1

theorem parameter_graph_domain_original (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ D.ball.domain) :
    (ApproximationSequence.CM.oldCompactPeriods K D, z) ∈ parameterGraphDomain K D := by
  refine ⟨hz, ?_⟩
  rw [parameter_graph_bottom_original K D z hz, Matrix.det_one]
  exact one_ne_zero

theorem parameter_period_chart_holomorphic :
    DifferentiableOn ℂ (parameterPeriodChart K D) (parameterGraphDomain K D) :=
  CoordinateProjector.CM.projector_graph_chart_holomorphic _ _
    (ParameterProjectorAnalytic.CM.parameter_coordinate_projector_joint_holomorphic K D).differentiableOn
    ((initial_parameter_period_holomorphic K D).mono (fun _ h => h.1)) (fun _ h => h.2)

theorem parameter_period_chart_original (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ D.ball.domain) :
    parameterPeriodChart K D (ApproximationSequence.CM.oldCompactPeriods K D, z) = (PeriodLimit.CM.initialTotalPeriod K D z).matrix := by
  unfold parameterPeriodChart
  rw [ParameterProjectorAnalytic.CM.parameter_coordinate_projector_original]
  exact (ProjectorCharts.CM.projector_chart_at_base _ _
    (CoordinateProjector.CM.coordinate_projector_graph_fixed K _ _ (PeriodLimit.CM.initialTotalPeriod K D z)
      (TotalProjector.CM.total_source_projector_graph_fixed K D.initialPeriods z hz))).2.2

theorem parameter_period_chart_approximation {ε : ℝ}
    (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε) (z : HeckeCycles.GeometricSource.CM.BallChart)
    (hq : (ApproximationSequence.CM.newCompactPeriods K D A, z) ∈ parameterGraphDomain K D) :
    parameterPeriodChart K D (ApproximationSequence.CM.newCompactPeriods K D A, z) = (MovingTotalPeriod.CM.approximationTotalPeriod K D A z).matrix := by
  apply ProjectorCharts.CM.projector_chart_of_graph
  · rw [ParameterProjectorAnalytic.CM.parameter_coordinate_projector_approximation]
    exact CoordinateProjector.CM.coordinate_projector_graph_image K _ _ (PeriodLimit.CM.initialTotalPeriod K D z).matrix
      (MovingTotalPeriod.CM.approximationTotalPeriod K D A z) (TotalProjector.CM.approximation_projector_graph_image K D A z hq.1)
  · exact hq.2

theorem parameter_period_chart_smooth :
    ContDiffOn ℝ ∞ (parameterPeriodChart K D) (parameterGraphDomain K D) :=
  (Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF.Constructions.HolomorphicDerivative.contDiffOn_infty_of_differentiableOn
    (parameter_graph_domain_open K D) (parameter_period_chart_holomorphic K D)).restrict_scalars ℝ

end

/-! ThetaCycle: an analytic square root of the actual graph-coordinate
transition determinant, normalized by the original two half-determinants. -/

open scoped Classical _root_.Matrix _root_.Topology ContDiff _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM Filter

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase)

def parameterHalfDetDomain : Set (ParameterPoint K D) :=
  {q | q ∈ parameterGraphDomain K D ∧ (parameterGraphBottom K D q).det ∈ Complex.slitPlane}

def parameterHalfDet (q : ParameterPoint K D) : ℂ :=
  ((D.initialPeriods 0).halfDet q.2 : ℂ) * ((D.initialPeriods 1).halfDet q.2 : ℂ) /
    Complex.sqrt (parameterGraphBottom K D q).det

theorem parameter_half_det_domain_open : IsOpen (parameterHalfDetDomain K D) := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  have hs : parameterBaseDomain K D ∈ 𝓝 q :=
    (D.ball.domain_isOpen.preimage continuous_snd).mem_nhds hq.1.1
  have hc : ContinuousAt (fun r => (parameterGraphBottom K D r).det) q :=
    ((MatrixCalculus.CM.matrix_determinant_holomorphic _ (parameter_graph_bottom_holomorphic K D)).differentiableAt hs).continuousAt
  exact inter_mem ((parameter_graph_domain_open K D).mem_nhds hq.1)
    (hc (Complex.isOpen_slitPlane.mem_nhds hq.2))

theorem parameter_half_det_domain_original (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ D.ball.domain) :
    (ApproximationSequence.CM.oldCompactPeriods K D, z) ∈ parameterHalfDetDomain K D := by
  refine ⟨parameter_graph_domain_original K D z hz, ?_⟩
  rw [parameter_graph_bottom_original K D z hz, Matrix.det_one]
  exact Complex.one_mem_slitPlane

theorem parameter_half_det_original (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ D.ball.domain) :
    parameterHalfDet K D (ApproximationSequence.CM.oldCompactPeriods K D, z) =
      ((D.initialPeriods 0).halfDet z : ℂ) * ((D.initialPeriods 1).halfDet z : ℂ) := by
  simp only [parameterHalfDet, parameter_graph_bottom_original K D z hz,
    Matrix.det_one, Complex.sqrt_one, div_one]

theorem parameter_half_det_square (q : ParameterPoint K D) :
    (parameterHalfDet K D q) ^ 2 =
      (((D.initialPeriods 0).halfDet q.2 : ℂ) * ((D.initialPeriods 1).halfDet q.2 : ℂ)) ^ 2 /
        (parameterGraphBottom K D q).det := by
  simp only [parameterHalfDet, div_pow, Complex.sqrt, Complex.cpow_ofNat_inv_pow]

theorem parameter_half_det_ne_zero (q : ParameterPoint K D)
    (hq : q ∈ parameterHalfDetDomain K D) : parameterHalfDet K D q ≠ 0 := by
  apply div_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))
  intro h
  have hs : (Complex.sqrt (parameterGraphBottom K D q).det) ^ 2 =
      (parameterGraphBottom K D q).det := Complex.cpow_ofNat_inv_pow _ 2
  rw [h, zero_pow (by decide)] at hs
  exact hq.1.2 hs.symm

theorem parameter_half_det_holomorphic :
    DifferentiableOn ℂ (parameterHalfDet K D) (parameterHalfDetDomain K D) := by
  have hh (i : Fin 2) : DifferentiableOn ℂ
      (fun q : ParameterPoint K D => ((D.initialPeriods i).halfDet q.2 : ℂ))
      (parameterHalfDetDomain K D) :=
    (D.initialPeriods i).halfDet_holomorphic.comp differentiableOn_snd (fun _ h => h.1.1)
  have hdet := (MatrixCalculus.CM.matrix_determinant_holomorphic _ (parameter_graph_bottom_holomorphic K D)).mono
    (show parameterHalfDetDomain K D ⊆ parameterBaseDomain K D from fun _ h => h.1.1)
  have hsqrt : DifferentiableOn ℂ
      (fun q => Complex.sqrt (parameterGraphBottom K D q).det) (parameterHalfDetDomain K D) :=
    (Complex.differentiableOn_sqrt.comp hdet (fun _ h => h.2))
  have hne : ∀ q ∈ parameterHalfDetDomain K D,
      Complex.sqrt (parameterGraphBottom K D q).det ≠ 0 := by
    intro q hq hzero
    have hs : (Complex.sqrt (parameterGraphBottom K D q).det) ^ 2 =
        (parameterGraphBottom K D q).det := Complex.cpow_ofNat_inv_pow _ 2
    rw [hzero, zero_pow (by decide)] at hs
    exact hq.1.2 hs.symm
  simpa only [parameterHalfDet, div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply] using!
    ((hh 0).mul (hh 1)).mul (hsqrt.inv hne)

theorem parameter_half_det_smooth :
    ContDiffOn ℝ ∞ (parameterHalfDet K D) (parameterHalfDetDomain K D) :=
  (Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF.Constructions.HolomorphicDerivative.contDiffOn_infty_of_differentiableOn
    (parameter_half_det_domain_open K D) (parameter_half_det_holomorphic K D)).restrict_scalars ℝ

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ParameterHalfDet.CM
