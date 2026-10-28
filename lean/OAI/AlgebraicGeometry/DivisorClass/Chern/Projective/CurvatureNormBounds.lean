import OAI.AlgebraicGeometry.DivisorClass.Chern.MixedCurvatureNorm
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BaseActionBounds

/-! # Curvature Norm Bounds -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Uniform zeroth-order bounds for the actual line and mixed curvature actions on compact original projective charts. -/

open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.CovectorConnectionOperator.lineOperator_formNormed Line.CovectorConnectionOperator.lineOperator_formSpace
  Line.CovectorConnectionOperator.lineOperator_endNormed Line.CovectorConnectionOperator.lineOperator_endSpace Line.CovectorConnectionOperator.lineOperator_directionNormed Line.CovectorConnectionOperator.lineOperator_directionSpace
  Line.CurvatureNorm.curvatureNorm_covectorNormed Line.CurvatureNorm.curvatureNorm_covectorSpace Line.CurvatureNorm.curvatureNorm_covectorComplex
  Line.CurvatureNorm.curvatureNorm_twoNormed Line.CurvatureNorm.curvatureNorm_twoSpace Line.CurvatureNorm.curvatureNorm_formComplex
  Projective.BaseActionBounds.baseBound_sharpNormed Projective.BaseActionBounds.baseBound_sharpSpace
  MixedCurvatureNorm.mixedCurv_baseEndNormed MixedCurvatureNorm.mixedCurv_baseEndSpace MixedCurvatureNorm.mixedCurv_actionNormed MixedCurvatureNorm.mixedCurv_actionSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineAndMixedCurvature_bound {T : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)}
    (hT : IsCompact T) (hTD : T ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ T, ∀ a : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1,
      let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
      let B := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z
      let F := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z
      ‖Line.CurvatureContraction.lineCurvatureAction b B F a‖ ≤ C * ‖a‖ ∧
        ‖Line.RoughAnti.lineCovectorMixedCurvatureTrace b 1 B (Holomorphic.CovectorCommutator.projectiveBaseConnectionCurvature V e z) F a‖ ≤ C * ‖a‖ := by
  obtain ⟨R, hR, hcurv⟩ := Projective.BaseCurvatureBounds.projectiveBaseConnectionCurvature_bound V e he hT hTD
  let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  let F := fun z => Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z
  let L := ‖Line.CovectorConnectionOperator.covectorActionOperator (E := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1‖
  let S := fun z => ∑ j, ‖b j‖ * ‖Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (b.coord j).toContinuousLinearMap‖
  have hS : ContinuousOn S T := by
    have ht := Analysis.HodgeTheory.Decomposition.KoszulSmooth.Constructions.bilinearMetricSharp_smoothOn (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e)
      (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he)
      (fun z hz => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz)
    apply continuousOn_finsetSum Finset.univ
    intro j _
    exact continuousOn_const.mul ((ht.clm_apply (contDiffOn_const (c := (b.coord j).toContinuousLinearMap))).continuousOn.mono hTD).norm
  have hF : ContinuousOn (fun z => AntiTwoFormCoefficients.twoFormBilinear (F z)) T :=
    (Line.CurvatureNorm.twoFormBilinear_continuous (E := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).comp_continuousOn
      ((Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm_smooth V e he 2 h.curvature).continuousOn.mono hTD)
  let Q := fun z => (L * R + ‖AntiTwoFormCoefficients.twoFormBilinear (F z)‖ + 1) * S z
  have hQ : ContinuousOn Q T := ((continuousOn_const.add hF.norm).add continuousOn_const).mul hS
  obtain ⟨C, hC⟩ := hT.bddAbove_image hQ
  refine ⟨max C 0 + 1, by positivity, fun z hz a => ?_⟩
  have hS0 : 0 ≤ S z := Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hQB : Q z ≤ max C 0 + 1 := (hC ⟨z, hz, rfl⟩).trans ((le_max_left C 0).trans (by linarith))
  have h1 : ‖AntiTwoFormCoefficients.twoFormBilinear (F z)‖ * S z ≤ Q z :=
    mul_le_mul_of_nonneg_right (by
      have hp : 0 ≤ L * R := mul_nonneg (norm_nonneg _) hR.le
      linarith) hS0
  have h2 : (L * R + ‖AntiTwoFormCoefficients.twoFormBilinear (F z)‖) * S z ≤ Q z :=
    mul_le_mul_of_nonneg_right (by linarith) hS0
  exact ⟨(Line.CurvatureNorm.lineCurvatureAction_norm_le b (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (F z) a).trans
      (mul_le_mul_of_nonneg_right (h1.trans hQB) (norm_nonneg a)),
    (MixedCurvatureNorm.lineCovectorMixedCurvatureTrace_norm b 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
      (Holomorphic.CovectorCommutator.projectiveBaseConnectionCurvature V e z) (F z) (hcurv z hz) a).trans
      (mul_le_mul_of_nonneg_right (h2.trans hQB) (norm_nonneg a))⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
