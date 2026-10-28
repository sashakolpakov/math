import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration
import Mathlib.Topology.Order.DenselyOrdered

/-! # Cube Pullback Locality -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.CubePullbackLocality

noncomputable section

/-!
# Locality of actual manifold-cube pullbacks and integrals

Two smooth manifold maps agreeing on the closed unit cube have the same
pulled-back forms there. Their germs and derivatives agree at interior points;
continuity of the pulled-back coefficients extends equality to the boundary.
The finite-product closure argument includes the zero-dimensional cube.
-/

open Set _root_.MeasureTheory OAI.AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes
open scoped _root_.Manifold ContDiff _root_.Topology

/-- The closed unit cube is the closure of its interior in every dimension,
including dimension zero. -/
theorem closure_interior_unitCube (n : ℕ) :
    closure (interior (StokesF.SingularCubeStokes.unitCube n)) = StokesF.SingularCubeStokes.unitCube n := by
  simp only [StokesF.SingularCubeStokes.unitCube, StokesF.Stokes.unitCube, ← pi_univ_Icc, interior_pi_set Set.finite_univ,
    closure_pi_set, closure_interior_Icc (show (0 : ℝ) ≠ 1 by norm_num)]

section GermLocality

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
variable {k : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- Pullback of an actual covector field depends only on the germ of the map.
No globally defined smooth extension is required for this local identity. -/
theorem normedManifoldPullback_eq_of_eventuallyEq
    (form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M k) {f g : V → M} {x : V}
    (hfg : f =ᶠ[𝓝 x] g) :
    (form.pullback f).toNormedSpace x = (form.pullback g).toNormedSpace x := by
  have hx : f x = g x := hfg.self_of_nhds
  have hd : (show V →L[ℝ] E from mfderiv (𝓘(ℝ, V)) (𝓘(ℝ, E)) f x) =
      (show V →L[ℝ] E from mfderiv (𝓘(ℝ, V)) (𝓘(ℝ, E)) g x) := hfg.mfderiv_eq
  ext v
  change form (f x) (fun i => (mfderiv (𝓘(ℝ, V)) (𝓘(ℝ, E)) f x) (v i)) =
    form (g x) (fun i => (mfderiv (𝓘(ℝ, V)) (𝓘(ℝ, E)) g x) (v i))
  rw [hx]
  congr 1
  funext i
  exact congrArg (fun L : V →L[ℝ] E => L (v i)) hd

end GermLocality

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold (𝓘(ℝ, E)) ∞ M] {n k : ℕ}

/-- Agreement on the closed cube gives equality of all pulled-back form
coefficients on the interior, where the maps have equal germs. -/
theorem manifoldCubePullback_congr_interior
    (sigma tau : ManifoldCubeIntegration.SmoothManifoldCube E M n)
    (h : EqOn sigma.toFun tau.toFun (StokesF.SingularCubeStokes.unitCube n))
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M k) :
    EqOn (ManifoldCubeIntegration.manifoldCubePullback sigma form) (ManifoldCubeIntegration.manifoldCubePullback tau form)
      (interior (StokesF.SingularCubeStokes.unitCube n)) := by
  intro x hx
  have hfg : sigma.toFun =ᶠ[𝓝 x] tau.toFun := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact h (interior_subset hy)
  exact normedManifoldPullback_eq_of_eventuallyEq (form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M k) hfg

/-- The actual pullbacks agree on the entire closed cube. Smoothness makes
their coefficients continuous, so equality extends to every boundary point. -/
theorem manifoldCubePullback_congr
    (sigma tau : ManifoldCubeIntegration.SmoothManifoldCube E M n)
    (h : EqOn sigma.toFun tau.toFun (StokesF.SingularCubeStokes.unitCube n))
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M k) :
    EqOn (ManifoldCubeIntegration.manifoldCubePullback sigma form) (ManifoldCubeIntegration.manifoldCubePullback tau form) (StokesF.SingularCubeStokes.unitCube n) := by
  have hc := (manifoldCubePullback_congr_interior sigma tau h form).closure
    (ManifoldCubeIntegration.manifoldCubePullback sigma form).smooth.continuous
    (ManifoldCubeIntegration.manifoldCubePullback tau form).smooth.continuous
  rwa [closure_interior_unitCube] at hc

/-- Integration of an actual smooth manifold top form depends only on the
map on the closed unit cube, not on its chosen smooth values outside it. -/
theorem manifoldCubeIntegration_congr
    (sigma tau : ManifoldCubeIntegration.SmoothManifoldCube E M n)
    (h : EqOn sigma.toFun tau.toFun (StokesF.SingularCubeStokes.unitCube n))
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    ManifoldCubeIntegration.manifoldCubeIntegration sigma form = ManifoldCubeIntegration.manifoldCubeIntegration tau form := by
  rw [ManifoldCubeIntegration.manifoldCubeIntegration_eq_integral, ManifoldCubeIntegration.manifoldCubeIntegration_eq_integral]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  exact congrArg (fun w : Analysis.DifferentialForms.Manifold.Basic.FormValue (Fin n → ℝ) n => w (fun j => Pi.single j 1))
    (manifoldCubePullback_congr sigma tau h form hx)

end

end OAI.AlgebraicTopology.DeRham.Comparison.CubePullbackLocality
