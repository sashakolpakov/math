import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CompactMetricCover
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NestedCutoffExistence

/-! # Finite Metric Cutoffs -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FiniteMetricCutoffs.CM.Construction

noncomputable section

/-! Finitely many actual real Schwartz chart cutoffs equal to one on
the compact pieces of the global metric cover. -/

open Set
open scoped SchwartzMap _root_.Topology

structure CompactMetricCutoffs (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) where
  cutoff : Fin C.size → 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)
  compact_support : ∀ i, HasCompactSupport (cutoff i : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ)
  supported : ∀ i, tsupport (cutoff i) ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V (C.chart i)
  one_on_compact : ∀ i, ∀ x ∈ C.compactSet i,
    cutoff i ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (C.chart i x)) = 1

theorem compactMetricCutoffs_nonempty (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) :
    Nonempty (CompactMetricCutoffs V C) := by
  have hlocal (i : Fin C.size) : ∃ g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ),
      HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) ∧
      tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V (C.chart i) ∧
      ∀ x ∈ C.compactSet i, g ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (C.chart i x)) = 1 := by
    let K := MetricChartMeasure.CM.Construction.varietyMetricChartCoordinates V (C.chart i) (C.compactSet i)
    have hK : IsCompact K := MetricMeasureFinite.CM.Construction.varietyMetricChartCoordinates_isCompact V (C.chart i)
      (C.isCompact i) (C.subset_source i)
    have hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V (C.chart i) :=
      fun z hz => ((MetricChartMeasure.CM.Construction.mem_varietyMetricChartCoordinates V (C.chart i) (C.compactSet i) z).mp hz).1
    obtain ⟨g, hgc, hgU, _, hg1⟩ := NestedCutoffExistence.CM.Construction.exists_real_schwartz_cutoff_near_compact hK
      (EuclideanMetric.CM.Construction.varietyEuclideanDomain V (C.chart i)).isOpen hKU
    refine ⟨g, hgc, hgU, fun x hx => ?_⟩
    have hz : (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (C.chart i x) ∈ K := by
      dsimp only [K]
      rw [MetricMeasureFinite.CM.Construction.varietyMetricChartCoordinates_eq_image V (C.chart i) (C.subset_source i)]
      exact mem_image_of_mem _ hx
    exact (hg1 _ hz).self_of_nhds
  choose g hgc hgU hg1 using hlocal
  exact ⟨⟨g, hgc, hgU, hg1⟩⟩

def projectiveMetricCutoffs (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) :
    CompactMetricCutoffs V C := Classical.choice (compactMetricCutoffs_nonempty V C)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FiniteMetricCutoffs.CM.Construction
