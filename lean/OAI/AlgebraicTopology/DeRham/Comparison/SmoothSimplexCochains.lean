import OAI.AlgebraicTopology.DeRham.Comparison.SimplicialCochainOfValues
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration
import OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback

/-! # Smooth Simplex Cochains -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains

noncomputable section

/-!
# Actual simplex integration in the existing cochain objects

The checked smooth-simplex integral is placed in the ordinary simplicial
cochain object through its proved function coordinates. Evaluation recovers
the integral itself, and the proved smooth-map naturality becomes naturality
of these degreewise cochain maps. Compatibility with the differential will
be supplied separately by the actual Stokes theorem.
-/

open _root_.CategoryTheory
open scoped Simplicial _root_.Manifold ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual integral as a morphism into the existing simplicial cochain
object in degree `n`. -/
def smoothSimplexCochain (n : ℕ) :
    (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M).X n ⟶
      (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).X n :=
  SimplicialCochainOfValues.simplicialCochainOfValues (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M)
    (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (ModuleCat.of ℂ ℂ)
    (SmoothSimplexIntegration.smoothSimplexIntegrationMap E M) n

@[simp]
theorem smoothSimplexCochain_function (n : ℕ) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    (Cohomology.Singular.Coefficients.degreewiseFunctionIso (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
      (ModuleCat.of ℂ ℂ) n).hom (smoothSimplexCochain E M n form) =
        SmoothSimplexIntegration.smoothSimplexIntegrationMap E M n form :=
  SimplicialCochainOfValues.simplicialCochainOfValues_function (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M)
    (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (ModuleCat.of ℂ ℂ)
    (SmoothSimplexIntegration.smoothSimplexIntegrationMap E M) n form

/-- The cochain value is precisely the checked Duffy simplex integral. -/
@[simp]
theorem smoothSimplexCochain_evaluation (n : ℕ) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌) :
    Cohomology.Singular.Coefficients.simplicialEvaluation (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
      (ModuleCat.of ℂ ℂ) sigma (smoothSimplexCochain E M n form) =
        SmoothSimplexIntegration.smoothSimplexIntegration sigma form := by
  rw [← Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply, smoothSimplexCochain_function]
  rfl

variable {E M}
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {N : Type} [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, F) ∞ N]

/-- The degreewise simplex integration maps are natural under genuine smooth
pullback of manifold forms and of smooth singular cochains. -/
theorem smoothSimplexCochain_naturality (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (n : ℕ) :
    (Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback f hf).f n ≫ smoothSimplexCochain E M n =
      smoothSimplexCochain F N n ≫
        (Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothPullback E F (ModuleCat.of ℂ ℂ) f hf).f n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm F N n at form
  apply (Cohomology.Singular.Coefficients.degreewiseFunctionIso (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
    (ModuleCat.of ℂ ℂ) n).toLinearEquiv.injective
  funext sigma
  change (Cohomology.Singular.Coefficients.degreewiseFunctionIso (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
      (ModuleCat.of ℂ ℂ) n).hom
      (smoothSimplexCochain E M n (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback f hf form)) sigma =
    (Cohomology.Singular.Coefficients.degreewiseFunctionIso (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
      (ModuleCat.of ℂ ℂ) n).hom
      ((Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ)
        (Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothSingularMap E F f hf)).f n
          (smoothSimplexCochain F N n form)) sigma
  rw [smoothSimplexCochain_function, Cohomology.Singular.Formulas.degreewiseFunctionIso_pullback,
    smoothSimplexCochain_function]
  exact (SmoothSimplexIntegration.smoothSimplexIntegration_postcompose f hf sigma form).symm

end

end OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains
