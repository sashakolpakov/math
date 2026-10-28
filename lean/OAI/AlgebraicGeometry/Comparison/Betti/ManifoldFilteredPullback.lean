import OAI.AlgebraicGeometry.Comparison.Betti.ManifoldFormFiltration
import OAI.Analysis.DifferentialForms.Manifold.PurePullback

/-! # Manifold Filtered Pullback -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ManifoldFilteredPullback.Hodge

noncomputable section

/-! Holomorphic pullback preserves the actual form filtration and commutes
with its finite type projectors. -/

open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E F M N : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℂ, E) ∞ M] [IsManifold 𝓘(ℂ, F) ∞ N]

theorem pureFormsInDegree_pullback (g : M → N)
    (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ g) (n : ℕ) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm F N n) (ha : a ∈ ManifoldFormFiltration.Hodge.pureFormsInDegree F N n i) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hg) a ∈
      ManifoldFormFiltration.Hodge.pureFormsInDegree E M n i := by
  rcases i with ⟨⟨p, q⟩, h⟩
  subst n
  exact Analysis.DifferentialForms.Manifold.PurePullback.complexPullback_mem_pureManifoldForm g hg ha

theorem manifoldFormFiltration_pullback (g : M → N)
    (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ g) (n : ℕ) (r : ℤ) :
    (ManifoldFormFiltration.Hodge.manifoldFormFiltration F N n r).map
        (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hg)) ≤
      ManifoldFormFiltration.Hodge.manifoldFormFiltration E M n r := by
  rw [Submodule.map_le_iff_le_comap]
  refine iSup_le fun i => iSup_le fun hi => ?_
  intro a ha
  apply Submodule.mem_iSup_of_mem i
  apply Submodule.mem_iSup_of_mem hi
  exact pureFormsInDegree_pullback g hg n i a ha

theorem manifoldTypeProjection_pullback [FiniteDimensional ℝ F] (g : M → N)
    (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ g) (n : ℕ) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm F N n) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hg)
        (ManifoldFormFiltration.Hodge.manifoldTypeProjection F N n i a) =
      ManifoldFormFiltration.Hodge.manifoldTypeProjection E M n i
        (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hg) a) := by
  have ha : a ∈ ⨆ j : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n, ManifoldFormFiltration.Hodge.pureFormsInDegree F N n j :=
    (ManifoldFormFiltration.Hodge.pureFormsInDegree_iSup F N n).symm ▸ Submodule.mem_top
  refine Submodule.iSup_induction (ManifoldFormFiltration.Hodge.pureFormsInDegree F N n)
    (motive := fun a => Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hg)
        (ManifoldFormFiltration.Hodge.manifoldTypeProjection F N n i a) =
      ManifoldFormFiltration.Hodge.manifoldTypeProjection E M n i
        (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hg) a)) ha ?_ ?_ ?_
  · intro j b hb
    have hpb := pureFormsInDegree_pullback g hg n j b hb
    by_cases hij : i = j
    · subst j
      rw [ManifoldFormFiltration.Hodge.manifoldTypeProjection_identity F N n i b hb,
        ManifoldFormFiltration.Hodge.manifoldTypeProjection_identity E M n i _ hpb]
    · rw [ManifoldFormFiltration.Hodge.manifoldTypeProjection_other F N n i j hij b hb,
        ManifoldFormFiltration.Hodge.manifoldTypeProjection_other E M n i j hij _ hpb, map_zero]
  · simp only [map_zero]
  · intro b c hb hc
    simp only [map_add, hb, hc]

end

end OAI.AlgebraicGeometry.Comparison.Betti.ManifoldFilteredPullback.Hodge
