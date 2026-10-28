import OAI.Analysis.PDE.Dirichlet.DensityPath
import OAI.Analysis.PDE.Dirichlet.Closed.Admissible

open Set Module
open scoped ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

/-- An actual smooth periodic zero-boundary solution at one parameter of
the affine density path. This records solutions; it does not postulate any. -/
structure SmoothPathSolution {n : ℕ} {P V ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    (r B₀ F₀ F₁ : CoordinateSpace n 4 → ℝ) where
  t : ℝ
  parameter : t ∈ Icc (0 : ℝ) 1
  u : CoordinateSpace n 4 → ℝ
  smooth : ContDiff ℝ 4 u
  periodic : LatticePeriodic e lat u
  zero : ∀ x, r x = 0 → u x = 0
  positive : ∀ x, r x < 0 →
    (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x)).PosDef
  equation : ∀ x, r x < 0 →
    OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) = densityPath F₀ F₁ t x

end OAI.Analysis.PDE.Dirichlet
