import OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexStokes

/-! # Simplex Integration Cochain -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain

noncomputable section

/-!
# Integration into actual smooth singular cochains

The genuine smooth-simplex integral, with its checked orientation, is a
cochain map from the actual manifold de Rham complex to the existing smooth
singular simplicial cochains. The cochain identity is the proved Stokes
theorem, interpreted through the checked alternating-face coboundary.
-/

open _root_.CategoryTheory
open scoped Simplicial _root_.Manifold ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Actual integration over genuine smooth singular simplices, with the
cochain identity supplied by the proved smooth-simplex Stokes theorem. -/
def smoothSimplexIntegrationCochainMap :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M ⟶ Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M :=
  SimplicialCochainOfValues.simplicialCochainMapOfValues (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M)
    (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (ModuleCat.of ℂ ℂ)
    (SmoothSimplexIntegration.smoothSimplexIntegrationMap E M) (by
      intro n form sigma
      change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n at form
      rw [Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex_d_apply]
      change SmoothSimplexIntegration.smoothSimplexIntegration sigma (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form) =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
          SmoothSimplexIntegration.smoothSimplexIntegration ((Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet.δ i sigma) form
      exact SmoothSimplexStokes.smoothSimplexStokes sigma form)

/-- Its degreewise components are the actual integration cochains. -/
@[simp]
theorem smoothSimplexIntegrationCochainMap_f (n : ℕ) :
    (smoothSimplexIntegrationCochainMap E M).f n = SmoothSimplexCochains.smoothSimplexCochain E M n := rfl

/-- Evaluating the actual integration cochain returns the integral over the
given genuine smooth singular simplex. -/
@[simp]
theorem smoothSimplexIntegrationCochainMap_evaluation (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌) :
    Cohomology.Singular.Coefficients.simplicialEvaluation (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
      (ModuleCat.of ℂ ℂ) sigma ((smoothSimplexIntegrationCochainMap E M).f n form) =
        SmoothSimplexIntegration.smoothSimplexIntegration sigma form :=
  SmoothSimplexCochains.smoothSimplexCochain_evaluation E M n form sigma

/-- The induced map on genuine de Rham and smooth singular cohomology. -/
def smoothSimplexIntegrationCohomologyMap (n : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology E M n ⟶
      (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).homology n :=
  HomologicalComplex.homologyMap (smoothSimplexIntegrationCochainMap E M) n

variable {E M}
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {N : Type} [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, F) ∞ N]

/-- Actual integration is natural under smooth manifold pullback. -/
theorem smoothSimplexIntegrationCochainMap_naturality (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback f hf ≫ smoothSimplexIntegrationCochainMap E M =
      smoothSimplexIntegrationCochainMap F N ≫
        Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothPullback E F (ModuleCat.of ℂ ℂ) f hf := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact SmoothSimplexCochains.smoothSimplexCochain_naturality f hf n

/-- The integration map on cohomology preserves actual smooth pullbacks. -/
theorem smoothSimplexIntegrationCohomologyMap_naturality (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (n : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback f hf n ≫
        smoothSimplexIntegrationCohomologyMap E M n =
      smoothSimplexIntegrationCohomologyMap F N n ≫
        HomologicalComplex.homologyMap
          (Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothPullback E F (ModuleCat.of ℂ ℂ) f hf) n := by
  change HomologicalComplex.homologyMap (Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback f hf) n ≫
      HomologicalComplex.homologyMap (smoothSimplexIntegrationCochainMap E M) n =
    HomologicalComplex.homologyMap (smoothSimplexIntegrationCochainMap F N) n ≫
      HomologicalComplex.homologyMap
        (Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothPullback E F (ModuleCat.of ℂ ℂ) f hf) n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    smoothSimplexIntegrationCochainMap_naturality]

end

end OAI.AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain
