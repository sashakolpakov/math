import OAI.AlgebraicGeometry.ComplexMultiplication.InvariantPullbackChart
import OAI.AlgebraicGeometry.ComplexMultiplication.ManifoldScalarRestriction
import OAI.Analysis.DifferentialForms.Manifold.Bidegree
import OAI.Analysis.DifferentialForms.Manifold.ComplexCharts
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! # Invariant Pullback -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.InvariantPullback

noncomputable section

/-! # Actual invariant one-form pullback and its complex chart derivative -/

open scoped _root_.Manifold ContDiff

attribute [local instance] OAI.Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E F M G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
  [Group G] [TopologicalSpace G] [ChartedSpace F G]
  [LieGroup 𝓘(ℂ, F) ω G] [LieGroup 𝓘(ℝ, F) ∞ G]

/-- An actual model covector is transported to the identity tangent by its preferred chart. -/
def complexInvariantIdentityCovector (α : F →L[ℂ] ℂ) :
    TangentSpace 𝓘(ℝ, F) (1 : G) [⋀^Fin 1]→L[ℝ] ℂ :=
  (OAI.Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector F α).compContinuousLinearMap
    (OAI.Analysis.DifferentialForms.Manifold.TangentCoordinates.preferredTangentEquiv (E := F) (1 : G)).toContinuousLinearMap

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [LieGroup 𝓘(ℝ, F) ∞ G] in
/-- The genuine translated source map is complex differentiable on every chart overlap. -/
theorem contDiffAt_invariantPullbackChartMap
    (f : M → G) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
    (c : OpenPartialHomeomorph M E) (d : OpenPartialHomeomorph G F)
    (hc : c ∈ atlas E M) (hd : d ∈ atlas F G)
    (h1 : (1 : G) ∈ d.source) {y : E} (hy : y ∈ c.target) :
    ContDiffAt ℂ ω (fun w => d ((f (c.symm y))⁻¹ * f (c.symm w))) y := by
  have hcinv : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω c.symm y :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc) hy
  have hfc : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) ω (f ∘ c.symm) y :=
    hf.contMDiffAt.comp y hcinv
  have ht : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) ω
      (fun w => (f (c.symm y))⁻¹ * f (c.symm w)) y :=
    (contMDiff_mul_left (I := 𝓘(ℂ, F)) (n := ω)
      (a := (f (c.symm y))⁻¹)).contMDiffAt.comp y hfc
  have hd' : ContMDiffAt 𝓘(ℂ, F) 𝓘(ℂ, F) ω d
      ((f (c.symm y))⁻¹ * f (c.symm y)) := by
    rw [inv_mul_cancel]
    exact contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hd) h1
  exact (hd'.comp y ht).contDiffAt

/-- The full actual real tangent pullback has exactly the complex holomorphic chart values. -/
theorem complexInvariantRawForm_pullback_inChart
    (α : F →L[ℂ] ℂ) (f : M → G)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
    (c : OpenPartialHomeomorph M E) (hc : c ∈ atlas E M)
    {y : E} (hy : y ∈ c.target) (v : Fin 1 → E) :
    ((AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantRawForm (complexInvariantIdentityCovector (G := G) α)).pullback f).inChart c y v =
      α (fderiv ℂ (fun w => (chartAt F (1 : G))
        ((f (c.symm y))⁻¹ * f (c.symm w))) y (v 0)) := by
  let d := chartAt F (1 : G)
  have hd : d ∈ atlas F G := chart_mem_atlas F _
  have h1 : (1 : G) ∈ d.source := mem_chart_source F _
  have hp := InvariantPullbackChart.invariantRawForm_pullback_inChart 1
    (complexInvariantIdentityCovector (G := G) α) f
    (ManifoldScalarRestriction.contMDiff_complex_to_real (hf.of_le le_top)) c d hc hd h1 hy
  rw [hp]
  have hcancel := OAI.Analysis.DifferentialForms.Manifold.Charts.chartTangentMap_comp_inverse d hd (d.map_source h1)
  rw [d.left_inv h1] at hcancel
  have hder := (contDiffAt_invariantPullbackChartMap f hf c d hc hd h1 hy).differentiableAt
    (by simp)
  change α (OAI.Analysis.DifferentialForms.Manifold.Charts.chartTangentMap d 1
    (OAI.Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap d (d 1)
      (fderiv ℝ (fun w => d ((f (c.symm y))⁻¹ * f (c.symm w))) y (v 0)))) = _
  rw [show OAI.Analysis.DifferentialForms.Manifold.Charts.chartTangentMap d 1 (OAI.Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap d (d 1)
      (fderiv ℝ (fun w => d ((f (c.symm y))⁻¹ * f (c.symm w))) y (v 0))) =
      fderiv ℝ (fun w => d ((f (c.symm y))⁻¹ * f (c.symm w))) y (v 0) from
    congrArg (fun linear => linear
      (fderiv ℝ (fun w => d ((f (c.symm y))⁻¹ * f (c.symm w))) y (v 0))) hcancel]
  rw [hder.fderiv_restrictScalars ℝ]
  rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.InvariantPullback
