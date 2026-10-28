import OAI.Analysis.HodgeTheory.Decomposition.MeasureVolume

/-! # Forward Chart -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.ForwardChart

noncomputable section

/-! Actual compact subsets of the original chart source and their literal Euclidean coordinate images. -/

open Set
open scoped _root_.Manifold
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  {K : Set V.analyticSpace} (hKs : K ⊆ e.source)

include hKs

theorem compact_forward_chart (hK : IsCompact K) : IsCompact (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e '' K) := by
  have hc : ContinuousOn (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e) e.source :=
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm.continuous.comp_continuousOn e.continuousOn
  exact hK.image_of_continuousOn (hc.mono hKs)

theorem forward_chart_subset_domain : Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e '' K ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := by
  rintro _ ⟨y, hy, rfl⟩
  exact Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward_mem V e y (hKs hy)

theorem inverse_forward_chart_image : Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e '' (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e '' K) = K := by
  rw [← image_comp]
  have heq : EqOn (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e ∘ Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e) id K :=
    fun y hy => Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse_forward V e y (hKs hy)
  exact (image_congr heq).trans (image_id K)

theorem point_not_in_forward_chart (x : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (hx : Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e x ∉ K) : x ∉ Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e '' K := by
  rintro ⟨y, hy, rfl⟩
  exact hx ((Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse_forward V e y (hKs hy)).symm ▸ hy)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.ForwardChart
