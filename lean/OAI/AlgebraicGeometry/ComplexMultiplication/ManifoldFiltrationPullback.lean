import OAI.AlgebraicGeometry.Comparison.Betti.ManifoldFormFiltration
import OAI.Analysis.DifferentialForms.Manifold.PurePullback

/-! # Manifold Filtration Pullback -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ManifoldFiltrationPullback

noncomputable section

/-! # Holomorphic pullback preserves the full genuine smooth Hodge filtration -/

open scoped _root_.Manifold ContDiff

open OAI.Analysis.DifferentialForms.Manifold.PurePullback OAI.AlgebraicGeometry.Comparison.Betti.ManifoldFormFiltration.Hodge

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E F M N : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℂ, E) ∞ M] [IsManifold 𝓘(ℂ, F) ∞ N]

/-- Every genuine smooth bidegree is retained by actual holomorphic tangent pullback. -/
theorem pureFormsInDegree_pullback (g : M → N)
    (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ g) (n : ℕ) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm F N n) (hf : form ∈ Comparison.Betti.ManifoldFormFiltration.Hodge.pureFormsInDegree F N n i) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hg) form ∈
      Comparison.Betti.ManifoldFormFiltration.Hodge.pureFormsInDegree E M n i := by
  rcases i with ⟨⟨p, q⟩, hi⟩
  subst n
  exact Analysis.DifferentialForms.Manifold.PurePullback.complexPullback_mem_pureManifoldForm g hg hf

/-- The sum of all genuine bidegrees with first degree at least `r` is retained. -/
theorem manifoldFormFiltration_pullback (g : M → N)
    (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ g) (n : ℕ) (r : ℤ)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm F N n) (hf : form ∈ Comparison.Betti.ManifoldFormFiltration.Hodge.manifoldFormFiltration F N n r) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hg) form ∈
      Comparison.Betti.ManifoldFormFiltration.Hodge.manifoldFormFiltration E M n r := by
  have h : Comparison.Betti.ManifoldFormFiltration.Hodge.manifoldFormFiltration F N n r ≤
      (Comparison.Betti.ManifoldFormFiltration.Hodge.manifoldFormFiltration E M n r).comap
        (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hg)) := by
    refine iSup_le fun i => iSup_le fun hi => ?_
    intro a ha
    apply Submodule.mem_iSup_of_mem i
    apply Submodule.mem_iSup_of_mem hi
    exact pureFormsInDegree_pullback g hg n i a ha
  exact h hf

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ManifoldFiltrationPullback
