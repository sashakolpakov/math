import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CutoffSymbolNorm
import OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorMetricOperatorBound

/-! # Cutoff Symbol Metric -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CutoffSymbolMetric

noncomputable section

/-! The fixed cutoff commutators are uniformly bounded in the original metric, independently of the line weight. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] BaseMetricBounds.basePair_metricNormed BaseMetricBounds.basePair_metricSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)

include he hf

theorem projectiveCutoffSymbols_metric_bound {T : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)}
    (hT : IsCompact T) (hTD : T ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ T, ∀ a : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1,
      let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
      let B := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z
      let ℓ := fderiv ℝ (fun y => f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e y)) z
      let d := Line.Cutoff.lineDolbeaultCutoffSymbol 1 ℓ a
      let s := Line.Cutoff.lineCodifferentialCutoffSymbol b 0 B ℓ a
      (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 2 B d d).re ≤ C * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B a a).re ∧
      (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 0 B s s).re ≤ C * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B a a).re := by
  let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  obtain ⟨R, hR, hRb⟩ := CutoffSymbolNorm.projectiveCutoffSymbols_norm_bound V e he f hf hT hTD
  obtain ⟨U0, hU0, hB0⟩ := CovectorMetricCutoffBound.bilinearFormMetricPair_uniform_upper b 0 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e)
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he) (fun z hz => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz)
    (fun z hz => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz) hT hTD
  obtain ⟨U2, hU2, hB2⟩ := CovectorMetricCutoffBound.bilinearFormMetricPair_uniform_upper b 2 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e)
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he) (fun z hz => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz)
    (fun z hz => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz) hT hTD
  obtain ⟨M, hMb⟩ := hT.bddAbove_image (((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).continuousOn.mono hTD).norm)
  let K := max M 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨(U0 + U2) * R ^ 2 * K, by positivity, fun z hz a => ?_⟩
  have hn : 0 ≤ (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) a a).re := by
    rw [Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair_eq_intrinsic b 1 _ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he (hTD hz))
      (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he (hTD hz))]
    exact Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair_nonneg 1 _
  have ha : ‖a‖ ^ 2 ≤ K * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) a a).re :=
    (OneCovectorMetricBound.oneCovectorMetric_norm_sq_le b _ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he (hTD hz))
      (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he (hTD hz)) a).trans
        (mul_le_mul_of_nonneg_right ((hMb ⟨z, hz, rfl⟩).trans (le_max_left _ _)) hn)
  have hd := CovectorMetricOperatorBound.bilinearFormMetricPair_between_degrees_bound b 2 _ a _ (U0 + U2) R K (by positivity) hR.le
    ((hB2 z hz _).trans (mul_le_mul_of_nonneg_right (by linarith : U2 ≤ U0 + U2) (sq_nonneg _))) (hRb z hz a).1 ha
  have hc := CovectorMetricOperatorBound.bilinearFormMetricPair_between_degrees_bound b 0 _ a _ (U0 + U2) R K (by positivity) hR.le
    ((hB0 z hz _).trans (mul_le_mul_of_nonneg_right (by linarith : U0 ≤ U0 + U2) (sq_nonneg _))) (hRb z hz a).2 ha
  exact ⟨hd, hc⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CutoffSymbolMetric
