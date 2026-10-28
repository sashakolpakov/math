import OAI.AlgebraicGeometry.DivisorClass.Chern.BochnerCurvature
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CurvatureNormBounds
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BaseMetricBounds

/-! # Curvature -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The exact curvature remainder in the original full Bochner formula is uniformly bounded in the original metric. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Projective.BaseActionBounds.baseBound_sharpNormed Projective.BaseActionBounds.baseBound_sharpSpace Projective.BaseMetricBounds.basePair_metricNormed Projective.BaseMetricBounds.basePair_metricSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.smoothDolbeaultLaplacianOne_full_curvature (i : V.analyticSpace)
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    let B := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e
    let G := Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e
    let A := h.projectiveConnectionChart V e i
    let f := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 ((h.smoothDolbeaultLaplacianOne V a).val i).extension z =
      (1 / 2 : ℂ) • Line.RoughAnti.lineCovectorFullRoughLaplacian b 1 B G A f z +
        BochnerCurvature.fullBochnerCurvatureAction b (B z) G z (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z) (f z) := by
  apply (h.smoothDolbeaultLaplacianOne_full_decomposition V e he i a hz).trans
  dsimp only [BochnerCurvature.fullBochnerCurvatureAction]
  rw [show Holomorphic.CovectorCommutator.projectiveBaseConnectionCurvature V e z = OperatorConnectionCurvature.operatorConnectionCurvature (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) z from rfl]
  abel

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveFullBochnerCurvature_bound {T : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)}
    (hT : IsCompact T) (hTD : T ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ T, ∀ a : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1,
      ‖BochnerCurvature.fullBochnerCurvatureAction (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
        (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) z
          (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z) a‖ ≤ C * ‖a‖ := by
  obtain ⟨C, hC, hb⟩ := Projective.BaseActionBounds.projectiveBaseCurvatureAction_bound V e he hT hTD
  obtain ⟨D, hD, hd⟩ := h.projectiveLineAndMixedCurvature_bound V e he hT hTD
  exact ⟨C + 2 * D, by positivity, fun z hz a =>
    BochnerCurvature.fullBochnerCurvatureAction_norm_of_bounds _ _ _ _ _ a C D (hb z hz a) (hd z hz a).1 (hd z hz a).2⟩

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveFullBochnerCurvature_pair_bound {T : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)}
    (hT : IsCompact T) (hTD : T ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ T, ∀ a : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1,
      let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
      let B := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z
      |(Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B
        (BochnerCurvature.fullBochnerCurvatureAction b B (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) z
          (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z) a) a).re| ≤ C * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B a a).re := by
  obtain ⟨R, hR, hb⟩ := h.projectiveFullBochnerCurvature_bound V e he hT hTD
  have hS := Analysis.HodgeTheory.Decomposition.KoszulSmooth.Constructions.bilinearMetricSharp_smoothOn (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e)
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he)
    (fun z hz => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz)
  have hc : ContinuousOn (fun z => 2 * ‖Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)‖ * R *
      ‖ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z‖) T :=
    ((continuousOn_const.mul ((hS.continuousOn.mono hTD).norm)).mul continuousOn_const).mul
      (((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).continuousOn.mono hTD).norm)
  obtain ⟨Q, hQ⟩ := hT.bddAbove_image hc
  refine ⟨max Q 0 + 1, by positivity, fun z hz a => ?_⟩
  have hp := OneCovectorMetricBound.oneCovectorMetric_pair_control (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he (hTD hz))
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he (hTD hz)) a _ R hR.le (hb z hz a)
  apply hp.trans
  apply mul_le_mul_of_nonneg_right
    ((hQ ⟨z, hz, rfl⟩).trans ((le_max_left Q 0).trans (by linarith)))
  rw [Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair_eq_intrinsic _ 1 _ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he (hTD hz))
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he (hTD hz))]
  exact Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair_nonneg 1 _

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
