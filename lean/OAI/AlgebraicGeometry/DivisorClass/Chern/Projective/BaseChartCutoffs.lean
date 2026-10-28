import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BaseSquarePartition
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.GlobalPairSmooth

/-! # Base Chart Cutoffs -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BaseChartCutoffs

noncomputable section

/-! Fixed compact smooth coordinate cutoffs representing the original base partition whose squares sum to one. -/

open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

def projectiveBaseChartCutoff (i : BasePartition.projectiveBaseFiniteCover V) : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ :=
  (GlobalPairSmooth.exists_projectiveRealChartCutoff V (chartAt V.analyticModel i.val) (chart_mem_atlas V.analyticModel i.val)
    (BaseSquarePartition.projectiveBaseSquarePartition V i) (BaseSquarePartition.projectiveBaseSquarePartition_smooth V i)
    (BaseSquarePartition.projectiveBaseSquarePartition_support V i)).choose

theorem projectiveBaseChartCutoff_smooth (i : BasePartition.projectiveBaseFiniteCover V) :
    ContDiff ℝ ∞ (projectiveBaseChartCutoff V i) :=
  (GlobalPairSmooth.exists_projectiveRealChartCutoff V (chartAt V.analyticModel i.val) (chart_mem_atlas V.analyticModel i.val)
    (BaseSquarePartition.projectiveBaseSquarePartition V i) (BaseSquarePartition.projectiveBaseSquarePartition_smooth V i)
    (BaseSquarePartition.projectiveBaseSquarePartition_support V i)).choose_spec.1

theorem projectiveBaseChartCutoff_compact (i : BasePartition.projectiveBaseFiniteCover V) :
    HasCompactSupport (projectiveBaseChartCutoff V i) :=
  (GlobalPairSmooth.exists_projectiveRealChartCutoff V (chartAt V.analyticModel i.val) (chart_mem_atlas V.analyticModel i.val)
    (BaseSquarePartition.projectiveBaseSquarePartition V i) (BaseSquarePartition.projectiveBaseSquarePartition_smooth V i)
    (BaseSquarePartition.projectiveBaseSquarePartition_support V i)).choose_spec.2.1

theorem projectiveBaseChartCutoff_support_image (i : BasePartition.projectiveBaseFiniteCover V) :
    tsupport (projectiveBaseChartCutoff V i) ⊆
      Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V (chartAt V.analyticModel i.val) '' tsupport (BaseSquarePartition.projectiveBaseSquarePartition V i) :=
  (GlobalPairSmooth.exists_projectiveRealChartCutoff V (chartAt V.analyticModel i.val) (chart_mem_atlas V.analyticModel i.val)
    (BaseSquarePartition.projectiveBaseSquarePartition V i) (BaseSquarePartition.projectiveBaseSquarePartition_smooth V i)
    (BaseSquarePartition.projectiveBaseSquarePartition_support V i)).choose_spec.2.2.1

theorem projectiveBaseChartCutoff_support (i : BasePartition.projectiveBaseFiniteCover V) :
    tsupport (projectiveBaseChartCutoff V i) ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V (chartAt V.analyticModel i.val) :=
  (GlobalPairSmooth.exists_projectiveRealChartCutoff V (chartAt V.analyticModel i.val) (chart_mem_atlas V.analyticModel i.val)
    (BaseSquarePartition.projectiveBaseSquarePartition V i) (BaseSquarePartition.projectiveBaseSquarePartition_smooth V i)
    (BaseSquarePartition.projectiveBaseSquarePartition_support V i)).choose_spec.2.2.2.1

theorem projectiveBaseChartCutoff_value (i : BasePartition.projectiveBaseFiniteCover V)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V (chartAt V.analyticModel i.val)) :
    projectiveBaseChartCutoff V i z =
      BaseSquarePartition.projectiveBaseSquarePartition V i (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V (chartAt V.analyticModel i.val) z) :=
  (GlobalPairSmooth.exists_projectiveRealChartCutoff V (chartAt V.analyticModel i.val) (chart_mem_atlas V.analyticModel i.val)
    (BaseSquarePartition.projectiveBaseSquarePartition V i) (BaseSquarePartition.projectiveBaseSquarePartition_smooth V i)
    (BaseSquarePartition.projectiveBaseSquarePartition_support V i)).choose_spec.2.2.2.2 z hz

theorem projectiveBaseChartCutoff_reconstruct (i : BasePartition.projectiveBaseFiniteCover V)
    {x : V.analyticSpace} (hx : x ∈ (chartAt V.analyticModel i.val).source) :
    projectiveBaseChartCutoff V i (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V (chartAt V.analyticModel i.val) x) =
      BaseSquarePartition.projectiveBaseSquarePartition V i x := by
  rw [projectiveBaseChartCutoff_value V i (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward_mem V _ x hx),
    Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse_forward V _ x hx]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BaseChartCutoffs
