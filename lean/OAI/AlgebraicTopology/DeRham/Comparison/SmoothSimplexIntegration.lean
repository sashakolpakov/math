import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldSimplexCube
import OAI.AlgebraicTopology.DeRham.Comparison.CubePullbackLocality
import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration
import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor

/-! # Smooth Simplex Integration -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration

noncomputable section

/-!
# Integration of manifold forms over genuine smooth singular simplices

The simplex has its existing meaning: a continuous singular simplex with a
smooth extension on an open neighborhood of the closed standard simplex.
The integral is the signed Duffy pullback integral over the unit cube. Its
value is proved independent of the global smooth cube chosen to extend that
parameterization, using equality on the closed cube alone.
-/

open _root_.CategoryTheory Opposite Set _root_.MeasureTheory OAI.AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes
open OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor
open scoped Simplicial _root_.Manifold ContDiff

variable {E F : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  {n : ℕ}

/-- The actual complex-linear integral of a manifold form over a smooth
singular simplex, with the Duffy parameterization's orientation corrected. -/
def smoothSimplexIntegration
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n →ₗ[ℂ] ℂ :=
  (-1 : ℝ) ^ n • ManifoldCubeIntegration.manifoldCubeIntegration (ManifoldSimplexCube.manifoldSimplexCube sigma)

@[simp]
theorem smoothSimplexIntegration_apply
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    smoothSimplexIntegration sigma form =
      (-1 : ℝ) ^ n • ManifoldCubeIntegration.manifoldCubeIntegration (ManifoldSimplexCube.manifoldSimplexCube sigma) form := rfl

/-- The definition is an ordinary complex Bochner integral of the actual
pulled-back form, multiplied by the Duffy orientation sign. -/
theorem smoothSimplexIntegration_eq_integral
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    smoothSimplexIntegration sigma form =
      (-1 : ℝ) ^ n •
        ∫ x in Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => 1),
          ManifoldCubeIntegration.manifoldCubePullback (ManifoldSimplexCube.manifoldSimplexCube sigma) form x
            (fun j => Pi.single j 1) := by
  rw [smoothSimplexIntegration_apply, ManifoldCubeIntegration.manifoldCubeIntegration_eq_integral]

/-- Any global smooth cube agreeing with the Duffy simplex on the closed unit
cube computes the same integral. Agreement on a neighborhood is not required. -/
theorem smoothSimplexIntegration_eq_cube
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (cube : ManifoldCubeIntegration.SmoothManifoldCube E M n)
    (hcube : ∀ t : StokesF.SingularCubeStokes.unitCube n, cube t.val =
      (TopCat.of M).toSSetObjEquiv _ sigma.val (DuffyCoordinates.Duffy.toSimplex n t))
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    smoothSimplexIntegration sigma form =
      (-1 : ℝ) ^ n • ManifoldCubeIntegration.manifoldCubeIntegration cube form := by
  have heq : Set.EqOn (ManifoldSimplexCube.manifoldSimplexCube sigma).toFun cube.toFun (StokesF.SingularCubeStokes.unitCube n) := by
    intro x hx
    exact (ManifoldSimplexCube.manifoldSimplexCube_apply sigma ⟨x, hx⟩).trans (hcube ⟨x, hx⟩).symm
  rw [smoothSimplexIntegration_apply,
    CubePullbackLocality.manifoldCubeIntegration_congr (ManifoldSimplexCube.manifoldSimplexCube sigma) cube heq form]

variable (E M) in
/-- Degreewise integration sends an actual smooth form to its values on all
genuine smooth singular simplices. -/
def smoothSimplexIntegrationMap (n : ℕ) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n →ₗ[ℂ]
      ((Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌ → ℂ) :=
  LinearMap.pi fun sigma => smoothSimplexIntegration sigma

@[simp]
theorem smoothSimplexIntegrationMap_apply (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌) :
    smoothSimplexIntegrationMap E M n form sigma = smoothSimplexIntegration sigma form := rfl

/-- Integration is natural for actual smooth manifold maps. The chosen
global cube extensions need only agree on their closed parameter cubes. -/
theorem smoothSimplexIntegration_postcompose (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm F N n) :
    smoothSimplexIntegration ((Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothSingularMap E F f hf).app _ sigma) form =
      smoothSimplexIntegration sigma (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback f hf form) := by
  have hcube : ∀ t : StokesF.SingularCubeStokes.unitCube n,
      ManifoldCubeIntegration.manifoldCubePostcompose f hf (ManifoldSimplexCube.manifoldSimplexCube sigma) t.val =
        (TopCat.of N).toSSetObjEquiv _
          ((Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothSingularMap E F f hf).app _ sigma).val (DuffyCoordinates.Duffy.toSimplex n t) := by
    intro t
    change f (ManifoldSimplexCube.manifoldSimplexCube sigma t.val) = _
    rw [ManifoldSimplexCube.manifoldSimplexCube_apply]
    rfl
  rw [smoothSimplexIntegration_eq_cube _
    (ManifoldCubeIntegration.manifoldCubePostcompose f hf (ManifoldSimplexCube.manifoldSimplexCube sigma)) hcube form,
    ManifoldCubeIntegration.manifoldCubeIntegration_postcompose, smoothSimplexIntegration_apply]

end

end OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration
