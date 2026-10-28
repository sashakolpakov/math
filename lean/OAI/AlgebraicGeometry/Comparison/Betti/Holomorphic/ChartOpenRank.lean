import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartModuleBases
import OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorExteriorEquiv

/-! # Chart Open Rank -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartOpenRank

noncomputable section

/-! Holomorphic form modules on any open contained in a chart have the ordinary binomial rank. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

omit [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem chartPreimage_image_eq (e : OpenPartialHomeomorph M E) (U : Opens M)
    (hU : (U : Set M) ⊆ e.source) : Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen e (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U) = U := by
  apply le_antisymm (Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimage_image_le e U)
  intro x hx
  exact ⟨hU hx, Analysis.DifferentialForms.Manifold.ChartEquiv.mem_chartImageOpen e U (hU hx) hx⟩

variable [FiniteDimensional ℂ E]

def chartContainedFormBasis (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (U : Opens M) (hU : (U : Set M) ⊆ e.source) (n : ℕ) :
    Module.Basis (Fin (Module.finrank ℂ (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0)))
      C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ), ℂ⟯ (DeRhamComplex.forms E U n) := by
  have h := chartPreimage_image_eq e U hU
  exact h ▸ ChartModuleBases.chartPreimageFormBasis e he (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U) (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen_le_target e U) n
    (FormFrames.holomorphicOpenFormsBasis (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U) n)

theorem chartContainedFormBasis_card (n : ℕ) :
    Nat.card (Fin (Module.finrank ℂ (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0))) =
      (Module.finrank ℂ E).choose n := by
  rw [Nat.card_fin, Pure.CovectorExteriorEquiv.Holomorphic.pureCovector_finrank]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartOpenRank
