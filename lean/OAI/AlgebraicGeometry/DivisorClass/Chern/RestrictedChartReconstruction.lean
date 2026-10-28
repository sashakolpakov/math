import OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectionChartDerivative
import OAI.Analysis.HodgeTheory.Decomposition.LocalAdjointForm

/-! # Restricted Chart Reconstruction -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.RestrictedChartReconstruction

noncomputable section

/-! Reconstruct actual smooth tangent covectors from coefficients on the precise chart and frame intersection. -/

open _root_.TopologicalSpace Filter
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section Reconstruction
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {n : ℕ}

theorem rawFromChart_smooth_onOpen (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (U : Opens M) (hU : U ≤ Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e) (form : Analysis.DifferentialForms.Manifold.Basic.RawForm E n)
    (hform : ContDiffOn ℝ ∞ form (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U : Set E)) :
    Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart e form) (U : Set M) := by
  intro f hf y hy
  have hye : f.symm y ∈ e.source := hU hy.2
  have hcoord : ContDiffAt ℝ ∞ (e ∘ f.symm) y :=
    Analysis.DifferentialForms.Manifold.Charts.contDiffAt_chart_transition f e hf he hy.1 hye
  have hpoint : e (f.symm y) ∈ Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U :=
    ⟨e.map_source hye, by
      change e.symm (e (f.symm y)) ∈ U
      rw [e.left_inv hye]
      exact hy.2⟩
  have hcoeff := hform.contDiffAt ((Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds hpoint)
  have hcomp : ContDiffAt ℝ ∞ (fun z => form (e (f.symm z))) y := hcoeff.comp y hcoord
  have hsmooth : ContDiffAt ℝ ∞ (fun z =>
      (form (e (f.symm z))).compContinuousLinearMap (fderiv ℝ (e ∘ f.symm) z)) y :=
    Analysis.DifferentialForms.Manifold.Alternatization.contDiffAt_alternating_compContinuousLinearMap hcomp (hcoord.fderiv_right (by simp))
  have heq : (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart e form).inChart f =ᶠ[𝓝 y] (fun z =>
      (form (e (f.symm z))).compContinuousLinearMap (fderiv ℝ (e ∘ f.symm) z)) := by
    filter_upwards [(f.isOpen_inter_preimage_symm e.open_source).mem_nhds ⟨hy.1, hye⟩] with z hz
    exact Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart_inChart e f he hf form hz.1 hz.2
  exact (hsmooth.congr_of_eventuallyEq heq).contDiffWithinAt
end Reconstruction

open OAI.Analysis.HodgeTheory.Decomposition.LocalAdjointForm.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (U : Opens V.analyticSpace) (n : ℕ)

theorem analyticFormOfEuclideanCoefficients_smooth_onOpen
    (c : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)
    (hc : ContDiffOn ℝ ∞ c (ConnectionChartDerivative.projectiveOpenChartDomain V e U : Set _)) :
    ContDiffOn ℝ ∞ (Analysis.HodgeTheory.Decomposition.LocalAdjointForm.Constructions.analyticFormOfEuclideanCoefficients V n c) (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U : Set _) := by
  apply ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.projectiveReferenceBasis V) n).symm.contDiff.restrict_scalars ℝ).comp_contDiffOn
  apply hc.comp ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm.contDiff.restrict_scalars ℝ).contDiffOn
  intro y hy
  change ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm y) ∈ Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U
  rwa [ContinuousLinearEquiv.apply_symm_apply]

include he

theorem chartFormOfEuclideanCoefficients_smooth_onOpen (hU : U ≤ Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e)
    (c : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)
    (hc : ContDiffOn ℝ ∞ c (ConnectionChartDerivative.projectiveOpenChartDomain V e U : Set _)) :
    Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn (Analysis.HodgeTheory.Decomposition.LocalAdjointForm.Constructions.chartFormOfEuclideanCoefficients V e n c) (U : Set _) :=
  rawFromChart_smooth_onOpen e he U hU _ (analyticFormOfEuclideanCoefficients_smooth_onOpen V e U n c hc)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.RestrictedChartReconstruction
