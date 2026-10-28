import OAI.AlgebraicTopology.DeRham.Comparison.ComplexCubeIntegration
import OAI.AlgebraicTopology.DeRham.Comparison.StokesF
import OAI.Analysis.DifferentialForms.Manifold.ExteriorDerivativeSmooth
import Mathlib.Basic.Complex.BigOperators

/-! # Complex Stokes -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ComplexStokes

noncomputable section

/-!
# Stokes' theorem for complex-valued forms on smooth singular cubes

This derives the complex theorem from the verified real theorem by projecting
to real and imaginary coefficients. All derivatives and integrals are the
actual analytic operations. No complex Stokes statement is assumed.
-/

open Set _root_.MeasureTheory OAI.AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes
open scoped ContDiff

variable {n m : ℕ}

/-- Cubical Stokes for actual smooth complex-valued differential forms. -/
theorem complexSingularStokes (σ : StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m)
    (form : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℂ)
    (hform : ContDiff ℝ ∞ form) :
    ComplexCubeIntegration.complexIntegrateForm σ (extDeriv form) =
      ∑ i : Fin (n + 1), (-1 : ℝ) ^ (i : ℕ) •
        (ComplexCubeIntegration.complexIntegrateForm (StokesF.SingularCubeStokes.singularFace σ i 1) form -
          ComplexCubeIntegration.complexIntegrateForm (StokesF.SingularCubeStokes.singularFace σ i 0) form) := by
  have hreal :
      (ComplexCubeIntegration.complexIntegrateForm σ (extDeriv form)).re =
        (∑ i : Fin (n + 1), (-1 : ℝ) ^ (i : ℕ) •
          (ComplexCubeIntegration.complexIntegrateForm (StokesF.SingularCubeStokes.singularFace σ i 1) form -
            ComplexCubeIntegration.complexIntegrateForm (StokesF.SingularCubeStokes.singularFace σ i 0) form)).re := by
    calc
      _ = StokesF.Stokes.integral σ (extDeriv (Analysis.DifferentialForms.Manifold.Coefficients.Comparison.realForm form)) := by
        change StokesF.Stokes.integral σ (Analysis.DifferentialForms.Manifold.Coefficients.Comparison.realForm (extDeriv form)) = _
        congr 1
        funext x
        exact (Analysis.DifferentialForms.Manifold.Coefficients.Comparison.extDeriv_realForm form
          ((hform.differentiable (by simp)).differentiableAt)).symm
      _ = ∑ i : Fin (n + 1), (-1 : ℝ) ^ i.val *
          (StokesF.Stokes.integral (StokesF.Stokes.face σ i 1) (Analysis.DifferentialForms.Manifold.Coefficients.Comparison.realForm form) -
            StokesF.Stokes.integral (StokesF.Stokes.face σ i 0) (Analysis.DifferentialForms.Manifold.Coefficients.Comparison.realForm form)) :=
        StokesF.Stokes.integral_derivative_cube σ (Analysis.DifferentialForms.Manifold.Coefficients.Comparison.realForm form) (Analysis.DifferentialForms.Manifold.Coefficients.Comparison.contDiff_realForm form hform)
      _ = _ := by
        simp only [Complex.re_sum, Complex.smul_re, Complex.sub_re,
          ComplexCubeIntegration.complexIntegrateForm_re, smul_eq_mul]
  have himag :
      (ComplexCubeIntegration.complexIntegrateForm σ (extDeriv form)).im =
        (∑ i : Fin (n + 1), (-1 : ℝ) ^ (i : ℕ) •
          (ComplexCubeIntegration.complexIntegrateForm (StokesF.SingularCubeStokes.singularFace σ i 1) form -
            ComplexCubeIntegration.complexIntegrateForm (StokesF.SingularCubeStokes.singularFace σ i 0) form)).im := by
    calc
      _ = StokesF.Stokes.integral σ (extDeriv (Analysis.DifferentialForms.Manifold.Coefficients.Comparison.imagForm form)) := by
        change StokesF.Stokes.integral σ (Analysis.DifferentialForms.Manifold.Coefficients.Comparison.imagForm (extDeriv form)) = _
        congr 1
        funext x
        exact (Analysis.DifferentialForms.Manifold.Coefficients.Comparison.extDeriv_imagForm form
          ((hform.differentiable (by simp)).differentiableAt)).symm
      _ = ∑ i : Fin (n + 1), (-1 : ℝ) ^ i.val *
          (StokesF.Stokes.integral (StokesF.Stokes.face σ i 1) (Analysis.DifferentialForms.Manifold.Coefficients.Comparison.imagForm form) -
            StokesF.Stokes.integral (StokesF.Stokes.face σ i 0) (Analysis.DifferentialForms.Manifold.Coefficients.Comparison.imagForm form)) :=
        StokesF.Stokes.integral_derivative_cube σ (Analysis.DifferentialForms.Manifold.Coefficients.Comparison.imagForm form) (Analysis.DifferentialForms.Manifold.Coefficients.Comparison.contDiff_imagForm form hform)
      _ = _ := by
        simp only [Complex.im_sum, Complex.smul_im, Complex.sub_im,
          ComplexCubeIntegration.complexIntegrateForm_im, smul_eq_mul]
  exact Complex.ext hreal himag

/-- The same identity written entirely using complex Bochner integrals. -/
theorem complexSingularStokes_integral (σ : StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m)
    (form : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℂ)
    (hform : ContDiff ℝ ∞ form) :
    (∫ x in Icc (fun _ : Fin (n + 1) => (0 : ℝ)) (fun _ => 1),
      ComplexCubeIntegration.complexCubeIntegrand σ (extDeriv form) x) =
      ∑ i : Fin (n + 1), (-1 : ℝ) ^ (i : ℕ) •
        ((∫ x in Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => 1),
          ComplexCubeIntegration.complexCubeIntegrand (StokesF.SingularCubeStokes.singularFace σ i 1) form x) -
        (∫ x in Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => 1),
          ComplexCubeIntegration.complexCubeIntegrand (StokesF.SingularCubeStokes.singularFace σ i 0) form x)) := by
  have h := complexSingularStokes σ form hform
  rw [ComplexCubeIntegration.complexIntegrateForm_eq_integral σ (extDeriv form)
    (Analysis.DifferentialForms.Manifold.ExteriorDerivativeSmooth.contDiff_extDeriv_infty hform)] at h
  simpa only [ComplexCubeIntegration.complexIntegrateForm_eq_integral _ form hform] using h

end

end OAI.AlgebraicTopology.DeRham.Comparison.ComplexStokes
