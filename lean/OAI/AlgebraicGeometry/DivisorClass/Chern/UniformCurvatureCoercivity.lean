import OAI.AlgebraicGeometry.DivisorClass.Chern.CurvatureCutoffThreshold
import OAI.AlgebraicGeometry.DivisorClass.Chern.BaseCutoffGlobal

/-! # Uniform Curvature Coercivity -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.UniformCurvatureCoercivity

noncomputable section

/-! One threshold depending only on the original projective base ensures native Dolbeault coercivity for every actual holomorphic line bundle metric above it. -/

open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem projective_exists_uniform_curvature_coercivity (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
      (h : HolomorphicMetric.Data.HolomorphicLineMetricData u),
      (∀ (x : V.analyticSpace) (v : TangentSpace 𝓘(ℝ, V.analyticModel) x), v ≠ 0 →
        C * (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re ≤
          ((Complex.I • h.curvature) x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re) →
      h.smoothDolbeaultOneCoercive V := by
  classical
  let bounds := fun i : Projective.BasePartition.projectiveBaseFiniteCover V =>
    CurvatureCutoffThreshold.projective_exists_curvature_cutoff_threshold V (chartAt V.analyticModel i.val)
      (chart_mem_atlas V.analyticModel i.val) (Projective.BaseChartCutoffs.projectiveBaseChartCutoff V i)
      (Projective.BaseChartCutoffs.projectiveBaseChartCutoff_smooth V i) (Projective.BaseChartCutoffs.projectiveBaseChartCutoff_compact V i)
      (Projective.BaseChartCutoffs.projectiveBaseChartCutoff_support V i) (Projective.BaseCutoffBounds.projectiveBaseTotalCutoffErrorBound V + 1)
  let C := fun i : Projective.BasePartition.projectiveBaseFiniteCover V => (bounds i).choose
  have hC : ∀ i, 0 < C i := fun i => (bounds i).choose_spec.1
  refine ⟨(∑ i, C i) + (Projective.BaseCutoffBounds.projectiveBaseTotalCutoffErrorBound V + 1), ?_, ?_⟩
  · have hsum := Finset.sum_nonneg (s := Finset.univ) (fun i _ => (hC i).le)
    have he := Projective.BaseCutoffBounds.projectiveBaseTotalCutoffErrorBound_pos V
    linarith only [hsum, he]
  · intro u h hF
    apply h.smoothDolbeaultOneCoercive_of_base_cutoffs V
    intro i
    apply (bounds i).choose_spec.2 u h
    intro x v hv
    have hi : C i ≤ ∑ j, C j :=
      Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)
    have hic : C i + (Projective.BaseCutoffBounds.projectiveBaseTotalCutoffErrorBound V + 1) ≤
        (∑ j, C j) + (Projective.BaseCutoffBounds.projectiveBaseTotalCutoffErrorBound V + 1) := by linarith only [hi]
    exact (mul_le_mul_of_nonneg_right hic
      (ComplexMultiplication.HodgeComparison.VarietyMetric.CM.Construction.varietyFubiniStudyForm_positive V x v hv).le).trans (hF x v hv)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.UniformCurvatureCoercivity
