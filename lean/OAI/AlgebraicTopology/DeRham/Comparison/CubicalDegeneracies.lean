import OAI.AlgebraicTopology.DeRham.Comparison.StokesF
import Mathlib.Data.Finsupp.Weight

/-! # Cubical Degeneracies -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.CubicalDegeneracies

/-!
# Why the smooth cubical chain complex still needs normalization

The imported Stokes theorem uses the free abelian group on all smooth cubes.
The following statements concern exactly that imported chain complex. They
show that it cannot yet be identified with ordinary singular chains: constant
cubes survive as cycles that are not boundaries in every positive degree.
The sum of all coefficients detects these classes.

One must quotient degenerate cubes, and establish the appropriate comparison,
before using this complex to represent ordinary singular cohomology.
-/

open OAI.AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes
open scoped ContDiff

variable {n m : ℕ}

/-- Every cubical boundary has coefficient sum zero. -/
theorem degree_singularBoundarySingle (σ : StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m) :
    Finsupp.degree (StokesF.SingularCubeStokes.singularBoundarySingle σ) = 0 := by
  classical
  simp [StokesF.SingularCubeStokes.singularBoundarySingle, StokesF.Stokes.boundaryGenerator, map_sum, pow_succ]

/-- The same augmentation obstruction holds for arbitrary finite chains. -/
theorem degree_singularBoundary (c : StokesF.SingularCubeStokes.SingularChain (n + 1) m) :
    Finsupp.degree (StokesF.SingularCubeStokes.singularBoundary c) = 0 := by
  classical
  change Finsupp.degree (Finsupp.linearCombination ℤ StokesF.Stokes.boundaryGenerator c) = 0
  rw [Finsupp.linearCombination_apply]
  change Finsupp.degree
    (c.support.sum fun σ => c σ • StokesF.Stokes.boundaryGenerator σ) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro σ _
  rw [map_zsmul, degree_singularBoundarySingle, smul_zero]

/-- No single cube with coefficient one can be a boundary in this complex. -/
theorem single_cube_not_boundary (σ : StokesF.SingularCubeStokes.SmoothSingularCube n m)
    (c : StokesF.SingularCubeStokes.SingularChain (n + 1) m) :
    StokesF.SingularCubeStokes.singularBoundary c ≠ Finsupp.single σ 1 := by
  intro h
  have hsum := congrArg Finsupp.degree h
  rw [degree_singularBoundary, Finsupp.degree_single] at hsum
  exact zero_ne_one hsum

/-- A globally constant map is an actual smooth cube. -/
def constantSmoothCube (n : ℕ) (x : Fin m → ℝ) : StokesF.SingularCubeStokes.SmoothSingularCube n m where
  toFun := fun _ => x
  smooth := contDiff_const

@[simp]
theorem singularFace_constantSmoothCube (x : Fin m → ℝ)
    (i : Fin (n + 1)) (ε : ℝ) :
    StokesF.SingularCubeStokes.singularFace (constantSmoothCube (n + 1) x) i ε = constantSmoothCube n x := by
  ext1
  rfl

/-- Every constant positive-dimensional cube is a cycle before normalization. -/
theorem singularBoundarySingle_constantSmoothCube (x : Fin m → ℝ) :
    StokesF.SingularCubeStokes.singularBoundarySingle (constantSmoothCube (n + 1) x) = 0 := by
  classical
  simp [StokesF.SingularCubeStokes.singularBoundarySingle, StokesF.Stokes.boundaryGenerator, pow_succ]

/-- In every positive degree, the imported unnormalized complex has a
concrete cycle that is not a boundary, even when the ambient space is a point. -/
theorem unnormalized_cubical_cycle_not_boundary (x : Fin m → ℝ) :
    ∃ c : StokesF.SingularCubeStokes.SingularChain (n + 1) m,
      StokesF.SingularCubeStokes.singularBoundary c = 0 ∧
      ∀ d : StokesF.SingularCubeStokes.SingularChain (n + 2) m, StokesF.SingularCubeStokes.singularBoundary d ≠ c := by
  refine ⟨Finsupp.single (constantSmoothCube (n + 1) x) 1, ?_, ?_⟩
  · change Finsupp.linearCombination ℤ StokesF.Stokes.boundaryGenerator
      (Finsupp.single (constantSmoothCube (n + 1) x) 1) = 0
    rw [Finsupp.linearCombination_single, one_smul]
    exact singularBoundarySingle_constantSmoothCube x
  · intro d hd
    have hdegree := congrArg Finsupp.degree hd
    exact zero_ne_one (by
      simpa only [degree_singularBoundary, Finsupp.degree_single] using hdegree)

end OAI.AlgebraicTopology.DeRham.Comparison.CubicalDegeneracies
