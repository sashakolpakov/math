import OAI.AlgebraicGeometry.DivisorClass.Chern.PointCutoffSectionData
import OAI.AlgebraicGeometry.DivisorClass.Chern.PointLogMetricEvaluation
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ZeroChartKernel
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CorrectionNonzero
import OAI.AlgebraicGeometry.DivisorClass.Chern.SmallPositiveParameter
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DolbeaultIntegralBound

/-! # Point Log Solver Nonzero -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.PointLogSolverNonzero

noncomputable section

section

/-! The constructed logarithmic solver family gives an actual global holomorphic section nonzero at the prescribed point. -/

open _root_.TopologicalSpace _root_.MeasureTheory _root_.Metric Set
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem projectivePointLogSolver_nonzero_section (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (i : V.analyticSpace)
    (x : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (hx : x ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (hc : ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 →
      (h.withPotential (PointLogMetricSolver.projectivePointLogPotential V e he x hx.1 (V.complexDimension + 1) ε hε)).hasBoundedSmoothDolbeaultPrimitives V) :
    ∃ s : HolomorphicSection.Data.HolomorphicLineSection u ⊤, s.val i ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e x, trivial, hx.2⟩ ≠ 0 := by
  have HS := PointCutoffSectionData.exists_projective_point_cutoff_section V h e he i x hx (V.complexDimension + 1)
  let a := HolomorphicLine.AntiForms.holomorphicLineAntiZeroEquiv u ⊤ HS.choose
  let U := HS.choose_spec.choose
  let M := HS.choose_spec.choose_spec.choose
  have hs := HS.choose_spec.choose_spec.choose_spec
  have HP := PointLogMetricEvaluation.projectivePointLogMetric_evaluation V h e he i x hx
  let R := HP.choose
  let c := HP.choose_spec.choose
  have hp := HP.choose_spec.choose_spec
  have hxU : x ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e
      (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) := ⟨hx.1, hs.1, hx.2⟩
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp
    ((ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen.mem_nhds hxU)
  have hρ : 0 < r / 2 := half_pos hr
  have hclosed : closedBall x (r / 2) ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e
      (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) :=
    (closedBall_subset_ball (half_lt_self hr)).trans hrU
  let A := c * (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).real (ball 0 1)
  let D : ℝ := 2 ^ (V.complexDimension + 1) * M
  have hA : 0 < A := mul_pos hp.2.1 CoordinateBallVolume.coordinateBall_unit_volume_pos
  have hD : 0 < D := mul_pos (pow_pos (by norm_num) _) hs.2.2.2.1
  obtain ⟨ε, hε, hε1, hεR, hερ, hεsmall⟩ := SmallPositiveParameter.exists_small_positive_parameter
    (R ^ 2) ((r / 2) ^ 2) A D (sq_pos_of_pos hp.1) (sq_pos_of_pos hρ) hA hD
  let φ := PointLogMetricSolver.projectivePointLogPotential V e he x hx.1 (V.complexDimension + 1) ε hε
  let B := (hc ε hε hε1) (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 a) (HolomorphicLine.Dolbeault.holomorphicLineDolbeault_squared u ⊤ 0 a)
  let b := B.choose
  have hb : HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 b = HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 a := B.choose_spec.1
  have hbn : ((h.withPotential φ).formIntegralPair V 0 b.val b.val).re ≤ M :=
    (Holomorphic.DolbeaultIntegralBound.holomorphicMetric_primitive_integral_bound V (h.withPotential φ) _ b B.choose_spec.2).trans
      (hs.2.2.2.2 ε hε hε1)
  have hbeq : HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ b.val = HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ a.val :=
    congrArg (fun t : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 => t.val) hb
  have hbU : HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict (le_top : U ≤ ⊤) (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ b.val) = 0 := by
    rw [hbeq]
    exact hs.2.2.1
  have hbf : DiffContOnCl ℂ (Holomorphic.ZeroChartPair.holomorphicLineZeroChart V e i b.val) (ball x (Real.sqrt ε)) :=
    Holomorphic.ZeroChartKernel.holomorphicLineZeroChart_local_kernel_ball V e he i U b.val hbU x (Real.sqrt ε)
      ((closedBall_subset_closedBall (Real.sqrt_le_iff.mpr ⟨hρ.le, hερ⟩)).trans hclosed)
  have hpoint := (hp.2.2.2 ε hε hεR b.val hbf).trans
    (mul_le_mul_of_nonneg_left hbn (mul_nonneg (pow_nonneg (by norm_num) _) hε.le))
  have hsmall : ‖Holomorphic.ZeroChartPair.holomorphicLineZeroChart V e i b.val x‖ < 1 := by
    have hsq : A * ‖Holomorphic.ZeroChartPair.holomorphicLineZeroChart V e i b.val x‖ ^ 2 < A := by
      calc
        _ = c * ((volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).real (ball 0 1) *
            ‖Holomorphic.ZeroChartPair.holomorphicLineZeroChart V e i b.val x‖ ^ 2) := by ring
        _ ≤ 2 ^ (V.complexDimension + 1) * ε * M := hpoint
        _ = D * ε := by ring
        _ < A := hεsmall
    have hsq1 : ‖Holomorphic.ZeroChartPair.holomorphicLineZeroChart V e i b.val x‖ ^ 2 < 1 :=
      (mul_lt_mul_iff_right₀ hA).mp (by simpa only [mul_one] using hsq)
    nlinarith [norm_nonneg (Holomorphic.ZeroChartPair.holomorphicLineZeroChart V e i b.val x)]
  exact Holomorphic.CorrectionNonzero.holomorphicLine_nonzero_section_of_small_correction V e i x hx a b hb hs.2.1 hsmall

end

/-! Every sufficiently positive original holomorphic twist has an actual global holomorphic section nonzero at any prescribed original point. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem positiveHolomorphicTwist_nonzero_at_point (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (y : V.analyticSpace) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∃ s : HolomorphicSection.Data.HolomorphicLineSection (u + n • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V) ⊤,
        s.val y ⟨y, trivial, (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace
          (u + n • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V)).mem_domain y⟩ ≠ 0 := by
  let e := chartAt V.analyticModel y
  have he : e ∈ atlas V.analyticModel V.analyticSpace := chart_mem_atlas V.analyticModel y
  have hye : y ∈ e.source := mem_chart_source V.analyticModel y
  let x := Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e y
  have hx : x ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward_mem V e y hye
  have hxy : Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e x = y := Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse_forward V e y hye
  have H := PointLogMetricSolver.projectivePointLogPotential_native_solvers V e he x hx (V.complexDimension + 1) h
  refine ⟨H.choose, H.choose_spec.1, fun n hn => ?_⟩
  have hdom := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace
    (u + n • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V)).mem_domain y
  have hxi : x ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace (u + n • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V) y) := by
    refine ⟨hx, ?_⟩
    change Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace
      (u + n • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V) y
    rw [hxy]
    exact hdom
  have HS := projectivePointLogSolver_nonzero_section V (Holomorphic.PositiveCurvature.positiveHolomorphicTwistMetric V u h n)
    e he y x hxi (H.choose_spec.2 n hn)
  refine ⟨HS.choose, fun hz => ?_⟩
  have hv : (⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e x, trivial, hxi.2⟩ :
      ↥(⊤ ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace (u + n • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V) y)) =
      ⟨y, trivial, hdom⟩ := Subtype.ext hxy
  exact HS.choose_spec ((congrArg (HS.choose.val y) hv).trans hz)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.PointLogSolverNonzero
