import OAI.AlgebraicTopology.DeRham.Comparison.ComplexNormalizedIntegration
import OAI.AlgebraicTopology.DeRham.Comparison.ComplexStokes
import OAI.AlgebraicTopology.DeRham.Comparison.StokesF
import Mathlib.Basic.Complex.BigOperators

/-! # Complex Chain Stokes -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ComplexChainStokes

noncomputable section

/-!
# Stokes' theorem on finite integral chains with complex coefficients

The complex cube identity extends to finite chains by linearity: the boundary
of each generator is the signed sum of its faces, and equality on generators
determines the two integral functionals.
-/

open OAI.AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes
open scoped ContDiff

variable {n m : ℕ}

theorem complexRawCubicalIntegration_re
    (form : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℂ)
    (c : StokesF.SingularCubeStokes.SingularChain n m) :
    (ComplexNormalizedIntegration.complexRawCubicalIntegration form c).re = StokesF.SingularCubeStokes.integrateChain c (Analysis.DifferentialForms.Manifold.Coefficients.Comparison.realForm form) := by
  simp [ComplexNormalizedIntegration.complexRawCubicalIntegration, Finsupp.linearCombination_apply, Finsupp.sum,
    StokesF.Stokes.chainIntegral, Complex.re_sum, zsmul_eq_mul]

theorem complexRawCubicalIntegration_im
    (form : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℂ)
    (c : StokesF.SingularCubeStokes.SingularChain n m) :
    (ComplexNormalizedIntegration.complexRawCubicalIntegration form c).im = StokesF.SingularCubeStokes.integrateChain c (Analysis.DifferentialForms.Manifold.Coefficients.Comparison.imagForm form) := by
  simp [ComplexNormalizedIntegration.complexRawCubicalIntegration, Finsupp.linearCombination_apply, Finsupp.sum,
    StokesF.Stokes.chainIntegral, Complex.im_sum, zsmul_eq_mul]

/-- Integration over the actual chain boundary equals integration of the
actual exterior derivative, for smooth complex-valued forms. -/
theorem complexRawCubicalIntegration_extDeriv
    (form : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℂ)
    (hform : ContDiff ℝ ∞ form) (c : StokesF.SingularCubeStokes.SingularChain (n + 1) m) :
    ComplexNormalizedIntegration.complexRawCubicalIntegration form (StokesF.SingularCubeStokes.singularBoundary c) =
      ComplexNormalizedIntegration.complexRawCubicalIntegration (extDeriv form) c := by
  classical
  have hgenerator (σ : StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m) :
      ComplexNormalizedIntegration.complexRawCubicalIntegration form (StokesF.Stokes.boundaryGenerator σ) =
        ComplexCubeIntegration.complexIntegrateForm σ (extDeriv form) := by
    rw [ComplexStokes.complexSingularStokes σ form hform]
    unfold StokesF.Stokes.boundaryGenerator
    simp only [map_sum, map_add, ComplexNormalizedIntegration.complexRawCubicalIntegration_single]
    apply Finset.sum_congr rfl
    intro i _
    simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one,
      pow_succ]
    push_cast
    ring
  have hlinear :
      (ComplexNormalizedIntegration.complexRawCubicalIntegration form).comp (StokesF.Stokes.boundaryLinear n m) =
        ComplexNormalizedIntegration.complexRawCubicalIntegration (extDeriv form) := by
    apply Finsupp.lhom_ext
    intro σ a
    change ComplexNormalizedIntegration.complexRawCubicalIntegration form
        (StokesF.Stokes.boundary (Finsupp.single σ a)) = _
    rw [StokesF.Stokes.boundary_generator, map_smul, hgenerator,
      ComplexNormalizedIntegration.complexRawCubicalIntegration_single]
  exact LinearMap.congr_fun hlinear c

end

end OAI.AlgebraicTopology.DeRham.Comparison.ComplexChainStokes
