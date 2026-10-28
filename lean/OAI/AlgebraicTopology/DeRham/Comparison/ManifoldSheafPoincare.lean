import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldSheafLocalPrimitives
import OAI.Analysis.DifferentialForms.Manifold.LocalPoincare

/-! # Manifold Sheaf Poincare -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ManifoldSheafPoincare

noncomputable section

/-!
# Exactness of the genuine manifold de Rham sheaf complex

The actual local Poincare theorem, transported through actual atlas charts,
supplies the local primitives required by the proved stalk exactness criterion.
This discharges that criterion without adding any geometric hypothesis beyond
a smooth manifold modeled on a finite-dimensional real normed space.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.Manifold ContDiff

universe u

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The analytic manifold Poincare theorem supplies actual local primitives. -/
theorem hasLocalSmoothManifoldPrimitives (n : ℕ) :
    ManifoldSheafLocalPrimitives.HasLocalSmoothManifoldPrimitives E M n := by
  intro U form hclosed x
  exact Analysis.DifferentialForms.Manifold.LocalPoincare.manifold_local_poincare U form hclosed x

/-- Consecutive actual exterior derivatives of manifold sheaves are exact in
every positive degree. -/
theorem manifoldDeRhamSheafStep_exact (n : ℕ) :
    (ManifoldSheafLocalPrimitives.manifoldDeRhamSheafStep E M n).Exact :=
  ManifoldSheafLocalPrimitives.manifoldDeRhamSheafStep_exact_of_local_primitives E M n
    (hasLocalSmoothManifoldPrimitives E M n)

/-- The genuine manifold de Rham sheaf complex is exact in positive degree. -/
theorem manifoldDeRhamSheafComplex_exactAt_succ (n : ℕ) :
    (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex E M).ExactAt (n + 1) :=
  ManifoldSheafLocalPrimitives.manifoldDeRhamSheafComplex_exactAt_of_local_primitives E M n
    (hasLocalSmoothManifoldPrimitives E M n)

/-- All positive-degree homology sheaves of the actual manifold de Rham
complex vanish. -/
theorem manifoldDeRhamSheafComplex_isZero_homology_succ (n : ℕ) :
    IsZero ((Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex E M).homology (n + 1)) :=
  (manifoldDeRhamSheafComplex_exactAt_succ E M n).isZero_homology

end

end OAI.AlgebraicTopology.DeRham.Comparison.ManifoldSheafPoincare
