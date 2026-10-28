import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.FrameScalarGlue
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ScalarExponential
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.LogConnection
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AdjointDerivative

/-! # Covector Transition -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

section

/-! The original transition function satisfies the differential gauge equation for the actual Chern connection. -/

open Filter _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveTransitionChart_connection (i j : V.analyticSpace)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i ⊓
        Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u j)) (v : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    fderiv ℝ (Projective.FrameScalarGlue.projectiveTransitionChart V u e i j) z v +
        Projective.FrameScalarGlue.projectiveTransitionChart V u e i j z * h.projectiveConnectionChart V e j z v =
      Projective.FrameScalarGlue.projectiveTransitionChart V u e i j z * h.projectiveConnectionChart V e i z v := by
  obtain ⟨W, hW, hxW, l, hl, _⟩ := h.localConnection_exists_log_overlap i j
    ⟨e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z), hz.2⟩
  let L := SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen l
  have hzW : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e W := ⟨hz.1, hxW⟩
  have heq : Projective.FrameScalarGlue.projectiveTransitionChart V u e i j =ᶠ[𝓝 z]
      Projective.BasePartition.projectiveScalarChart V e W (SmoothScalarExterior.smoothComplexOpenFunctionExp L) := by
    filter_upwards [(ConnectionChartDerivative.projectiveOpenChartDomain V e W).isOpen.mem_nhds hzW] with y hy
    rw [Projective.FrameScalarGlue.projectiveTransitionChart_apply V u e i j ⟨hy.1, hW hy.2⟩,
      Projective.BasePartition.projectiveScalarChart_apply V e W _ hy]
    exact hl ⟨e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V y), hy.2⟩
  have hd := Projective.ScalarExponential.projectiveScalarChart_exp_derivative V e he W L hzW v
  rw [← heq.fderiv_eq, ← heq.eq_of_nhds] at hd
  have hA := h.projectiveConnectionChart_log_overlap V e he i j W hW l hl hzW v
  rw [hd, hA]
  ring

end

/-! Full and antiholomorphic covariant derivatives of original bundle forms transform between the actual line frames. -/

open Filter _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.HessianBilinear.tensorConnection_formNormed Line.HessianBilinear.tensorConnection_formSpace
  Line.HessianBilinear.tensorConnection_oneNormed Line.HessianBilinear.tensorConnection_oneSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovectorDerivative_transition
    (U : Opens V.analyticSpace) (n : ℕ) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n)
    (i j : V.analyticSpace) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i ⊓
        Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u j))) :
    Line.ConnectionSymbols.lineCovectorConnectionDerivative n (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e)
        (h.projectiveConnectionChart V e j) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val j).extension) z =
      Projective.FrameScalarGlue.projectiveTransitionChart V u e i j z •
        Line.ConnectionSymbols.lineCovectorConnectionDerivative n (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e)
          (h.projectiveConnectionChart V e i) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val i).extension) z := by
  let W := ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓
    (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i ⊓
      Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u j))
  have heq : Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val j).extension =ᶠ[𝓝 z]
      (fun y => Projective.FrameScalarGlue.projectiveTransitionChart V u e i j y • Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val i).extension y) := by
    filter_upwards [W.isOpen.mem_nhds hz] with y hy
    exact Projective.FrameScalarGlue.holomorphicLineSmoothForm_transition_chart V u e U n a i j hy
  rw [Holomorphic.AdjointDerivative.lineCovectorConnectionDerivative_congr n (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e)
    (h.projectiveConnectionChart V e j) _ _ heq]
  apply Line.Cutoff.lineCovectorConnectionDerivative_gauge
  · exact ((Projective.FrameScalarGlue.projectiveTransitionChart_smooth V u e he i j).contDiffAt
      ((ConnectionChartDerivative.projectiveOpenChartDomain V e _).isOpen.mem_nhds ⟨hz.1, hz.2.2⟩)).differentiableAt (by simp)
  · exact ((ConnectionChartDerivative.projectiveOpenChartForm_smooth V e he _ n (a.val i)).contDiffAt
      ((ConnectionChartDerivative.projectiveOpenChartDomain V e _).isOpen.mem_nhds ⟨hz.1, hz.2.1, hz.2.2.1⟩)).differentiableAt (by simp)
  · exact h.projectiveTransitionChart_connection V e he i j ⟨hz.1, hz.2.2⟩

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveAntiDerivative_transition
    (U : Opens V.analyticSpace) (n : ℕ) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n)
    (i j : V.analyticSpace) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i ⊓
        Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u j))) :
    Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n)
        (Line.ConnectionSymbols.lineCovectorConnectionDerivative n (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e)
          (h.projectiveConnectionChart V e j) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val j).extension) z) =
      Projective.FrameScalarGlue.projectiveTransitionChart V u e i j z •
        Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n)
          (Line.ConnectionSymbols.lineCovectorConnectionDerivative n (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e)
            (h.projectiveConnectionChart V e i) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val i).extension) z) := by
  rw [h.projectiveCovectorDerivative_transition V e he U n a i j hz, map_smul]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
