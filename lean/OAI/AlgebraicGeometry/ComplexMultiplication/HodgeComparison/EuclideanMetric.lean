import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.InverseMetric
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Euclidean Metric -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction

noncomputable section

/-! Projective metric coefficients in Hilbert-space coordinates used by the
Fourier and Sobolev constructions. The coordinate change is complex linear. -/

open scoped ContDiff _root_.Manifold
open Set _root_.TopologicalSpace

abbrev varietyEuclideanModel (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :=
  EuclideanSpace ℂ (Fin V.complexDimension)

def varietyEuclideanCoordinates (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    varietyEuclideanModel V ≃L[ℂ] V.analyticModel :=
  PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin V.complexDimension => ℂ)

def varietyEuclideanDomain (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) : Opens (varietyEuclideanModel V) :=
  ⟨varietyEuclideanCoordinates V ⁻¹' e.target, e.open_target.preimage (varietyEuclideanCoordinates V).continuous⟩

theorem varietyEuclideanCoordinates_mapsTo (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) :
    MapsTo (varietyEuclideanCoordinates V) (varietyEuclideanDomain V e : Set (varietyEuclideanModel V))
      e.target := fun _ hz => hz

def varietyEuclideanMetric (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (z : varietyEuclideanModel V) :
    varietyEuclideanModel V →L[ℝ] varietyEuclideanModel V →L[ℝ] ℝ :=
  KahlerDifferential.CM.Construction.metricFromTwoForm
    (((IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V : OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace 2).inChart e
      (varietyEuclideanCoordinates V z)).compContinuousLinearMap
      ((varietyEuclideanCoordinates V).toContinuousLinearMap.restrictScalars ℝ))

theorem varietyEuclideanMetric_apply (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (z u v : varietyEuclideanModel V) :
    varietyEuclideanMetric V e z u v = KahlerDifferential.CM.Construction.varietyMetricInChart V e (varietyEuclideanCoordinates V z)
      (varietyEuclideanCoordinates V u) (varietyEuclideanCoordinates V v) :=
  KahlerDifferential.CM.Construction.metricFromTwoForm_pullback
    ((IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V : OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace 2).inChart e
      (varietyEuclideanCoordinates V z)) (varietyEuclideanCoordinates V).toContinuousLinearMap u v

theorem varietyEuclideanMetric_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) :
    ContDiffOn ℝ ∞ (varietyEuclideanMetric V e) (varietyEuclideanDomain V e : Set (varietyEuclideanModel V)) := by
  have hform : ContDiffOn ℝ ∞
      ((IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V : OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace 2).inChart e) e.target := by
    simpa only [OAI.Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain, Set.preimage_univ, Set.inter_univ] using
      (IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V).smooth e he
  have hL : ContDiffOn ℝ ∞ (varietyEuclideanCoordinates V)
      (varietyEuclideanDomain V e : Set (varietyEuclideanModel V)) :=
    (varietyEuclideanCoordinates V).contDiff.restrict_scalars ℝ |>.contDiffOn
  have hcomp := hform.comp hL (varietyEuclideanCoordinates_mapsTo V e)
  have hraw : ContDiffOn ℝ ∞
      (fun z => ((IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V : OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace 2).inChart e
        (varietyEuclideanCoordinates V z)).compContinuousLinearMap
        ((varietyEuclideanCoordinates V).toContinuousLinearMap.restrictScalars ℝ))
      (varietyEuclideanDomain V e : Set (varietyEuclideanModel V)) :=
    OAI.Analysis.DifferentialForms.Manifold.Alternatization.contDiffOn_alternating_compContinuousLinearMap hcomp contDiffOn_const
  exact (KahlerDifferential.CM.Construction.metricFromTwoForm_smooth (E := varietyEuclideanModel V)).comp_contDiffOn hraw

theorem varietyEuclideanMetric_positive (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) {z : varietyEuclideanModel V}
    (hz : z ∈ varietyEuclideanDomain V e) (u : varietyEuclideanModel V) (hu : u ≠ 0) :
    0 < varietyEuclideanMetric V e z u u := by
  rw [varietyEuclideanMetric_apply]
  apply KahlerDifferential.CM.Construction.varietyMetricInChart_positive V e he hz
  exact fun h => hu ((varietyEuclideanCoordinates V).injective
    (h.trans (varietyEuclideanCoordinates V).map_zero.symm))

theorem varietyEuclideanMetric_symmetric (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) {z : varietyEuclideanModel V}
    (hz : z ∈ varietyEuclideanDomain V e) (u v : varietyEuclideanModel V) :
    varietyEuclideanMetric V e z u v = varietyEuclideanMetric V e z v u := by
  rw [varietyEuclideanMetric_apply, varietyEuclideanMetric_apply]
  exact KahlerDifferential.CM.Construction.varietyMetricInChart_symmetric V e he hz _ _

def varietyEuclideanInverseMetric (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (z : varietyEuclideanModel V) :
    varietyEuclideanModel V →L[ℝ] varietyEuclideanModel V →L[ℝ] ℝ :=
  InverseMetric.CM.Construction.inverseBilinearForm (varietyEuclideanMetric V e z)

theorem varietyEuclideanInverseMetric_positive (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) {z : varietyEuclideanModel V}
    (hz : z ∈ varietyEuclideanDomain V e) (u : varietyEuclideanModel V) (hu : u ≠ 0) :
    0 < varietyEuclideanInverseMetric V e z u u :=
  InverseMetric.CM.Construction.inverseBilinearForm_positive _ (varietyEuclideanMetric_positive V e he hz) u hu

theorem varietyEuclideanInverseMetric_symmetric (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) {z : varietyEuclideanModel V}
    (hz : z ∈ varietyEuclideanDomain V e) (u v : varietyEuclideanModel V) :
    varietyEuclideanInverseMetric V e z u v = varietyEuclideanInverseMetric V e z v u :=
  InverseMetric.CM.Construction.inverseBilinearForm_symmetric _ (varietyEuclideanMetric_positive V e he hz)
    (varietyEuclideanMetric_symmetric V e he hz) u v

theorem varietyEuclideanInverseMetric_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) :
    ContDiffOn ℝ ∞ (varietyEuclideanInverseMetric V e)
      (varietyEuclideanDomain V e : Set (varietyEuclideanModel V)) := by
  have hInv := InverseMetric.CM.Construction.positive_bilinear_inverse_smoothOn (varietyEuclideanMetric V e)
    (varietyEuclideanDomain V e).isOpen (varietyEuclideanMetric_smooth V e he)
    (fun z hz => varietyEuclideanMetric_positive V e he hz)
  have hD : ContDiffOn ℝ ∞ (fun _ : varietyEuclideanModel V =>
      (InnerProductSpace.toDual ℝ (varietyEuclideanModel V)).toContinuousLinearEquiv.toContinuousLinearMap)
      (varietyEuclideanDomain V e : Set (varietyEuclideanModel V)) := contDiffOn_const
  exact hD.clm_comp hInv

theorem varietyEuclideanInverseMetric_uniform_bounds (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set (varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ varietyEuclideanDomain V e) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ z ∈ K, ∀ u : varietyEuclideanModel V,
        c * ‖u‖ * ‖u‖ ≤ varietyEuclideanInverseMetric V e z u u) ∧
      (∀ z ∈ K, ∀ u v : varietyEuclideanModel V,
        |varietyEuclideanInverseMetric V e z u v| ≤ C * ‖u‖ * ‖v‖) := by
  have hcont := (varietyEuclideanInverseMetric_smooth V e he).continuousOn.mono hKU
  obtain ⟨c, hc, hclow⟩ := MetricBounds.CM.Construction.positive_bilinear_uniform_lower_bound (varietyEuclideanInverseMetric V e) hK hcont
    (fun z hz => varietyEuclideanInverseMetric_positive V e he (hKU hz))
  obtain ⟨C, hC, hCup⟩ := MetricBounds.CM.Construction.bilinear_uniform_upper_bound (varietyEuclideanInverseMetric V e) hK hcont
  exact ⟨c, C, hc, hC, hclow, hCup⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction
