import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartMaps
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.HolomorphicPullback

/-! # Chart Iso -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartIso

noncomputable section

/-! Actual holomorphic coordinate changes identify the complexes on corresponding chart opens. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

def chartInverseToPreimage (e : OpenPartialHomeomorph M E) (V : Opens E)
    (hV : V ≤ Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) : V → Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen e V :=
  fun y => ⟨e.symm y, Analysis.DifferentialForms.Manifold.ChartEquiv.mem_chartPreimageOpen_symm e V hV y.property⟩

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem chartInverseToPreimage_holomorphic (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (V : Opens E) (hV : V ≤ Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ (chartInverseToPreimage e V hV) := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  exact ChartMaps.chartInverse_holomorphic e he V hV

omit [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem chartInverseToPreimage_forward (e : OpenPartialHomeomorph M E)
    (V : Opens E) (hV : V ≤ Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) :
    chartInverseToPreimage e V hV ∘ ChartMaps.chartForward e V = id := by
  funext x
  apply Subtype.ext
  exact e.left_inv x.property.1

omit [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem chartForward_inverseToPreimage (e : OpenPartialHomeomorph M E)
    (V : Opens E) (hV : V ≤ Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) :
    ChartMaps.chartForward e V ∘ chartInverseToPreimage e V hV = id := by
  funext y
  apply Subtype.ext
  exact e.right_inv (hV y.property)

def chartComplexIso (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (V : Opens E) (hV : V ≤ Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) :
    DeRhamComplex.complex E (Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen e V) ≅ DeRhamComplex.complex E V where
  hom := HolomorphicPullback.pullbackCochainMap (chartInverseToPreimage e V hV) (chartInverseToPreimage_holomorphic e he V hV)
  inv := HolomorphicPullback.pullbackCochainMap (ChartMaps.chartForward e V) (ChartMaps.chartForward_holomorphic e he V)
  hom_inv_id := by
    rw [← HolomorphicPullback.pullbackCochainMap_comp]
    have hi := chartInverseToPreimage_forward e V hV
    simpa only [hi] using (HolomorphicPullback.pullbackCochainMap_id (E := E) (M := Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen e V))
  inv_hom_id := by
    rw [← HolomorphicPullback.pullbackCochainMap_comp]
    have hi := chartForward_inverseToPreimage e V hV
    simpa only [hi] using (HolomorphicPullback.pullbackCochainMap_id (E := E) (M := V))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartIso
