import OAI.Analysis.DifferentialForms.Manifold.ChartEquiv
import OAI.Analysis.DifferentialForms.Manifold.ComplexCharts

/-! # Chart Maps -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartMaps

noncomputable section

/-! Actual holomorphic maps between a coordinate open and its chart preimage. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

def chartForward (e : OpenPartialHomeomorph M E) (V : Opens E) :
    Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen e V → V := fun x => ⟨e x, x.property.2⟩

def chartInverse (e : OpenPartialHomeomorph M E) (V : Opens E) : V → M :=
  fun y => e.symm y

theorem chartForward_holomorphic (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (V : Opens E) : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ (chartForward e V) := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  intro x
  apply contMDiffAt_subtype_iff.mpr
  exact contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) x.property.1

theorem chartInverse_holomorphic (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (V : Opens E) (hV : V ≤ Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ (chartInverse e V) := by
  intro y
  apply contMDiffAt_subtype_iff.mpr
  exact contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) (hV y.property)

omit [NormedSpace ℂ E] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem chartInverse_inclusion_forward (e : OpenPartialHomeomorph M E)
    {V W : Opens E} (h : W ≤ V) :
    chartInverse e V ∘ Opens.inclusion h ∘ chartForward e W =
      (Subtype.val : Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen e W → M) := by
  funext x
  exact e.left_inv x.property.1

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartMaps
