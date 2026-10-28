import OAI.AlgebraicTopology.DeRham.Comparison.ComplexChainStokes
import OAI.AlgebraicTopology.DeRham.Comparison.CubicalDegenerateQ
import OAI.Analysis.DifferentialForms.Manifold.ExteriorDerivative

/-! # Complex Normalized Stokes -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ComplexNormalizedStokes

noncomputable section

/-!
# The normalized cubical integration cochain map

The coboundary is precomposition with the actual normalized cubical boundary.
Stokes' theorem shows that integration intertwines it with the actual exterior
derivative on smooth complex-valued differential forms.
-/

open OAI.AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes
open scoped ContDiff

variable {n m : ℕ}

/-- Complex cochains on the genuine normalized integral cubical chain group. -/
abbrev NormalizedComplexCubicalCochain (n m : ℕ) :=
  CubicalDegenerateQ.NormalizedCubicalChain n m →ₗ[ℤ] ℂ

/-- The complex-linear coboundary induced by the actual normalized boundary. -/
def normalizedComplexCoboundary (n m : ℕ) :
    NormalizedComplexCubicalCochain n m →ₗ[ℂ]
      NormalizedComplexCubicalCochain (n + 1) m where
  toFun phi := phi.comp (CubicalDegenerateQ.normalizedBoundary n m)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem normalizedComplexCoboundary_apply
    (phi : NormalizedComplexCubicalCochain n m)
    (c : CubicalDegenerateQ.NormalizedCubicalChain (n + 1) m) :
    normalizedComplexCoboundary n m phi c = phi (CubicalDegenerateQ.normalizedBoundary n m c) := rfl

/-- The normalized complex coboundary has square zero. -/
theorem normalizedComplexCoboundary_squared
    (phi : NormalizedComplexCubicalCochain n m) :
    normalizedComplexCoboundary (n + 1) m (normalizedComplexCoboundary n m phi) = 0 := by
  apply LinearMap.ext
  intro c
  change phi (CubicalDegenerateQ.normalizedBoundary n m (CubicalDegenerateQ.normalizedBoundary (n + 1) m c)) = 0
  rw [CubicalDegenerateQ.normalizedBoundary_sq_zero, map_zero]

/-- Stokes' theorem descends to the quotient by actual degenerate cubes. -/
theorem normalizedComplexIntegration_extDeriv
    (form : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℂ)
    (hform : ContDiff ℝ ∞ form) :
    normalizedComplexCoboundary n m (ComplexNormalizedIntegration.normalizedComplexIntegration form) =
      ComplexNormalizedIntegration.normalizedComplexIntegration (extDeriv form) := by
  apply LinearMap.ext
  intro c
  obtain ⟨raw, rfl⟩ := (CubicalDegenerateQ.degenerateSubmodule (n + 1) m).mkQ_surjective c
  rw [normalizedComplexCoboundary_apply, CubicalDegenerateQ.normalizedBoundary_mk,
    ComplexNormalizedIntegration.normalizedComplexIntegration_mkQ, ComplexNormalizedIntegration.normalizedComplexIntegration_mkQ]
  exact ComplexChainStokes.complexRawCubicalIntegration_extDeriv form hform raw

/-- Integration is compatible with the bundled differential on genuine
smooth complex forms, as an equality of complex-linear maps. -/
theorem normalizedComplexIntegrationLinearMap_d :
    (normalizedComplexCoboundary n m).comp
      (ComplexNormalizedIntegration.normalizedComplexIntegrationLinearMap (n := n) (m := m)) =
    (ComplexNormalizedIntegration.normalizedComplexIntegrationLinearMap (n := n + 1) (m := m)).comp
      (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d (E := Fin m → ℝ) (n := n)) := by
  apply LinearMap.ext
  intro form
  exact normalizedComplexIntegration_extDeriv form form.smooth

end

end OAI.AlgebraicTopology.DeRham.Comparison.ComplexNormalizedStokes
