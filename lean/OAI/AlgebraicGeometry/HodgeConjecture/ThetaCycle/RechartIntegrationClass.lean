import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealModelForms
import OAI.AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain
import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor

/-! # Rechart Integration Class -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RechartIntegrationClass.CM

noncomputable section

/-! ThetaCycle: changing only the real model coordinates preserves the actual
continuous-singular class represented by a closed form. -/

open _root_.CategoryTheory OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor OAI.AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain
open scoped _root_.Manifold ContDiff

variable {E F M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem linear_rechart_preserves_betti_representation (e : E ≃L[ℝ] F) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n)
    (β : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) (TopCat.of M) n)
    (hβ : HomologicalComplex.homologyMap
      (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M) n β =
        AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCohomologyMap E M n (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M n form)) :
    let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
    let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
    HomologicalComplex.homologyMap
      (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction F (ModuleCat.of ℂ ℂ) M) n β =
        AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCohomologyMap F M n
          (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass F M n (RealModelForms.CM.linearRechartClosedForms e n form)) := by
  let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
  let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
  let g := (RealModelCharts.CM.linearRechartDiffeomorph (M := M) e ∞).symm
  have hg : (TopCat.ofHom ⟨(g : M → M), g.contMDiff.continuous⟩ : TopCat.of M ⟶ TopCat.of M) =
      𝟙 (TopCat.of M) := by
    ext x
    rfl
  have hr := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothCochainRestriction_naturality (ModuleCat.of ℂ ℂ) g g.contMDiff)
  rw [hg, AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_id, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_id, Category.id_comp,
    HomologicalComplex.homologyMap_comp] at hr
  have hi := AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCohomologyMap_naturality g g.contMDiff n
  have hc := Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldDeRhamFormClass_pullback_apply g g.contMDiff n form
  have hrβ := ConcreteCategory.congr_hom hr β
  have hif := ConcreteCategory.congr_hom hi (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M n form)
  change AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCohomologyMap F M n
      (Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback g g.contMDiff n (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M n form)) =
    HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothPullback F E (ModuleCat.of ℂ ℂ) g g.contMDiff) n
      (AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCohomologyMap E M n (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M n form)) at hif
  change HomologicalComplex.homologyMap
      (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction F (ModuleCat.of ℂ ℂ) M) n β =
    HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothPullback F E (ModuleCat.of ℂ ℂ) g g.contMDiff) n
      (HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M) n β) at hrβ
  rw [hβ] at hrβ
  rw [← hif, hc] at hrβ
  exact hrβ

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RechartIntegrationClass.CM
