import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CovectorCommutator
import OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectionCurvatureBounds

/-! # Base Curvature Bounds -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BaseCurvatureBounds

noncomputable section

/-! Base-curvature bounds in the original projective charts, independent of every line metric and twist. -/

open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.CovectorConnectionOperator.lineOperator_formNormed Line.CovectorConnectionOperator.lineOperator_formSpace
  Line.CovectorConnectionOperator.lineOperator_endNormed Line.CovectorConnectionOperator.lineOperator_endSpace Line.CovectorConnectionOperator.lineOperator_directionNormed Line.CovectorConnectionOperator.lineOperator_directionSpace
  ConnectionCurvatureBounds.curvatureBounds_endNormed ConnectionCurvatureBounds.curvatureBounds_endSpace ConnectionCurvatureBounds.curvatureBounds_directionNormed ConnectionCurvatureBounds.curvatureBounds_directionSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem projectiveBaseConnectionCurvature_bound {T : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)}
    (hT : IsCompact T) (hTD : T ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ T, ∀ v w : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V,
      ‖Holomorphic.CovectorCommutator.projectiveBaseConnectionCurvature V e z v w‖ ≤ C * ‖v‖ * ‖w‖ :=
  ConnectionCurvatureBounds.operatorConnectionCurvature_bound_on_compact (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e)
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen (Analysis.HodgeTheory.Decomposition.ProjectiveConnectionSmooth.Constructions.projectiveConnectionCoefficient_smooth V e he) hT hTD

theorem projectiveBaseCovectorCurvature_bound {T : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)}
    (hT : IsCompact T) (hTD : T ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ T, ∀ v w : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ∀ a : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1,
      ‖Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1 (Holomorphic.CovectorCommutator.projectiveBaseConnectionCurvature V e z v w) a‖ ≤
        C * ‖v‖ * ‖w‖ * ‖a‖ := by
  obtain ⟨B, hB, hb⟩ := projectiveBaseConnectionCurvature_bound V e he hT hTD
  let L := Line.CovectorConnectionOperator.covectorActionOperator (E := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1
  refine ⟨(‖L‖ + 1) * B, by positivity, ?_⟩
  intro z hz v w a
  calc
    ‖Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1 (Holomorphic.CovectorCommutator.projectiveBaseConnectionCurvature V e z v w) a‖ ≤
        ‖L‖ * ‖Holomorphic.CovectorCommutator.projectiveBaseConnectionCurvature V e z v w‖ * ‖a‖ :=
      ((L (Holomorphic.CovectorCommutator.projectiveBaseConnectionCurvature V e z v w)).le_opNorm a).trans
        (mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg a))
    _ ≤ (‖L‖ + 1) * (B * ‖v‖ * ‖w‖) * ‖a‖ := by
      gcongr
      · linarith
      · exact hb z hz v w
    _ = _ := by ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BaseCurvatureBounds
