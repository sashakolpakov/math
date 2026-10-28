import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Cutoff
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.GlobalPairSmooth
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BaseMetricBounds

/-! # Cutoff Symbol Norm -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CutoffSymbolNorm

noncomputable section

/-! Fixed base-chart cutoff symbols have uniform bounds independent of the line metric. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open _root_.ContinuousAlternatingMap

attribute [local instance] Line.HessianBilinear.tensorConnection_formNormed Line.HessianBilinear.tensorConnection_formSpace
  Line.HessianBilinear.tensorConnection_oneNormed Line.HessianBilinear.tensorConnection_oneSpace BaseActionBounds.baseBound_sharpNormed BaseActionBounds.baseBound_sharpSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)

include he hf

theorem projectiveCutoffSymbols_norm_bound {T : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)}
    (hT : IsCompact T) (hTD : T ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ T, ∀ a : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1,
      ‖Line.Cutoff.lineDolbeaultCutoffSymbol 1 (fderiv ℝ (fun y => f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e y)) z) a‖ ≤ C * ‖a‖ ∧
      ‖Line.Cutoff.lineCodifferentialCutoffSymbol (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 0
        (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (fderiv ℝ (fun y => f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e y)) z) a‖ ≤ C * ‖a‖ := by
  let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  let L : ℝ := ‖alternatizeUncurryFinCLM (n := 1) ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) ℂ‖ *
    ‖Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1)‖
  let S := fun z => ∑ j, ‖b j‖ * ‖Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (b.coord j).toContinuousLinearMap‖
  let ℓ := fderiv ℝ (fun y => f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e y))
  have hℓ : ContinuousOn ℓ T :=
    ((GlobalPairSmooth.projectiveGlobalScalar_smooth V e he f hf).fderiv_of_isOpen (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen
      (m := ∞) (by simp)).continuousOn.mono hTD
  have hsharp := (Analysis.HodgeTheory.Decomposition.KoszulSmooth.Constructions.bilinearMetricSharp_smoothOn (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e)
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he)
    (fun z hz => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz)).continuousOn.mono hTD
  have hS : ContinuousOn S T := continuousOn_finsetSum _ (fun j _ =>
    continuousOn_const.mul ((hsharp.clm_apply continuousOn_const).norm))
  have hQ : ContinuousOn (fun z => ‖ℓ z‖ * (L + S z)) T := hℓ.norm.mul (continuousOn_const.add hS)
  obtain ⟨R, hR⟩ := hT.bddAbove_image hQ
  refine ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun z hz a => ?_⟩
  have hL : 0 ≤ L := mul_nonneg (norm_nonneg (alternatizeUncurryFinCLM (n := 1) ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) ℂ))
    (ContinuousLinearMap.opNorm_nonneg (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1)))
  have hSn : 0 ≤ S z := Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hb : ‖ℓ z‖ * (L + S z) ≤ max R 1 := (hR ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  have hd : L * ‖ℓ z‖ ≤ max R 1 := by nlinarith [norm_nonneg (ℓ z)]
  have hc : ‖ℓ z‖ * S z ≤ max R 1 := by nlinarith [norm_nonneg (ℓ z)]
  exact ⟨(Line.Cutoff.lineDolbeaultCutoffSymbol_norm 1 (ℓ z) a).trans (mul_le_mul_of_nonneg_right hd (norm_nonneg a)),
    (Line.Cutoff.lineCodifferentialCutoffSymbol_norm b 0 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (ℓ z) a).trans
      (mul_le_mul_of_nonneg_right hc (norm_nonneg a))⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CutoffSymbolNorm
