import OAI.AlgebraicTopology.DeRham.Comparison.CubicalDegeneracyOperators
import OAI.AlgebraicTopology.DeRham.Comparison.ComplexCubeIntegration

/-! # Cubical Degenerate Integration -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.CubicalDegenerateIntegration

noncomputable section

/-!
# Integration vanishes on actual degenerate smooth cubes

Coordinate deletion has zero derivative in the deleted direction. The true
alternating pullback therefore vanishes on a degenerate cube, before integration.
This is the analytic input for descending to normalized cubical chains.
-/

open Set _root_.MeasureTheory OAI.AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes
open scoped ContDiff

variable {n m : ℕ}

/-- The deleted parameter direction has zero derivative in a degenerate cube. -/
theorem fderiv_cubeDegeneracy_basis (sigma : StokesF.SingularCubeStokes.SmoothSingularCube n m)
    (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    fderiv ℝ (CubicalDegeneracyOperators.cubeDegeneracy sigma i).toFun x (Pi.single i 1) = 0 := by
  change fderiv ℝ (sigma.toFun ∘ CubicalDegeneracyOperators.forgetCoordinate i) x (Pi.single i 1) = 0
  rw [fderiv_comp x
    ((sigma.smooth.differentiable (by simp)).differentiableAt)
    (CubicalDegeneracyOperators.forgetCoordinate i).differentiableAt]
  simp

/-- A vanishing parameter derivative makes the alternating pullback identically zero. -/
theorem integrateForm_zero_of_fderiv_coordinate_zero
    (sigma : StokesF.SingularCubeStokes.SmoothSingularCube n m) (i : Fin n)
    (hi : ∀ x, fderiv ℝ sigma.toFun x (Pi.single i 1) = 0)
    (form : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℝ) :
    StokesF.SingularCubeStokes.integrateForm sigma form = 0 := by
  have hzero : ∀ x, StokesF.SingularCubeStokes.pullbackForm sigma form x (fun j => Pi.single j 1) = 0 := by
    intro x
    change form (sigma.toFun x) (fun j => fderiv ℝ sigma.toFun x (Pi.single j 1)) = 0
    exact (form (sigma.toFun x)).map_coord_zero i (hi x)
  simp only [StokesF.Stokes.integral, hzero, integral_zero]

/-- Real differential forms integrate to zero over a coordinate-degenerate cube. -/
@[simp]
theorem integrateForm_cubeDegeneracy (sigma : StokesF.SingularCubeStokes.SmoothSingularCube n m)
    (i : Fin (n + 1))
    (form : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin (n + 1)]→L[ℝ] ℝ) :
    StokesF.SingularCubeStokes.integrateForm (CubicalDegeneracyOperators.cubeDegeneracy sigma i) form = 0 :=
  integrateForm_zero_of_fderiv_coordinate_zero _ i
    (fderiv_cubeDegeneracy_basis sigma i) form

/-- The complex pullback coefficient also vanishes pointwise on a degenerate cube. -/
@[simp]
theorem complexCubeIntegrand_cubeDegeneracy (sigma : StokesF.SingularCubeStokes.SmoothSingularCube n m)
    (i : Fin (n + 1))
    (form : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin (n + 1)]→L[ℝ] ℂ)
    (x : Fin (n + 1) → ℝ) :
    ComplexCubeIntegration.complexCubeIntegrand (CubicalDegeneracyOperators.cubeDegeneracy sigma i) form x = 0 := by
  exact (form ((CubicalDegeneracyOperators.cubeDegeneracy sigma i).toFun x)).map_coord_zero i
    (fderiv_cubeDegeneracy_basis sigma i x)

/-- Complex differential forms integrate to zero over a degenerate cube. -/
@[simp]
theorem complexIntegrateForm_cubeDegeneracy (sigma : StokesF.SingularCubeStokes.SmoothSingularCube n m)
    (i : Fin (n + 1))
    (form : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin (n + 1)]→L[ℝ] ℂ) :
    ComplexCubeIntegration.complexIntegrateForm (CubicalDegeneracyOperators.cubeDegeneracy sigma i) form = 0 := by
  apply Complex.ext <;> simp

end

end OAI.AlgebraicTopology.DeRham.Comparison.CubicalDegenerateIntegration
