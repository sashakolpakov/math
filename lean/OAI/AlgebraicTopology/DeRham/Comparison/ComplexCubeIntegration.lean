import OAI.Analysis.DifferentialForms.Manifold.Coefficients
import OAI.Analysis.DifferentialForms.Manifold.Basic
import OAI.AlgebraicTopology.DeRham.Comparison.StokesF
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Classes

/-! # Complex Cube Integration -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ComplexCubeIntegration

noncomputable section

/-!
# Complex-valued integration over smooth singular cubes

The integral is formed from its real and imaginary parts. For every smooth
form, `complexIntegrateForm_eq_integral` identifies it with the ordinary
complex Bochner integral of the genuine pullback evaluated on the standard
coordinate frame. Thus the component construction adds no new integration
axiom and uses the same orientation as the real cubical Stokes theorem.
-/

open Set _root_.MeasureTheory OAI.AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes
open scoped ContDiff

variable {d m : ℕ}

/-- The coefficient of the genuine pullback in the standard oriented frame. -/
def complexCubeIntegrand (σ : StokesF.SingularCubeStokes.SmoothSingularCube d m)
    (form : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin d]→L[ℝ] ℂ)
    (x : Fin d → ℝ) : ℂ :=
  form (σ.toFun x) (fun j => fderiv ℝ σ.toFun x (Pi.single j 1))

/-- The complex integral whose components are the real integrals. -/
def complexIntegrateForm (σ : StokesF.SingularCubeStokes.SmoothSingularCube d m)
    (form : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin d]→L[ℝ] ℂ) : ℂ :=
  ⟨StokesF.SingularCubeStokes.integrateForm σ (OAI.Analysis.DifferentialForms.Manifold.Coefficients.Comparison.realForm form), StokesF.SingularCubeStokes.integrateForm σ (OAI.Analysis.DifferentialForms.Manifold.Coefficients.Comparison.imagForm form)⟩

@[simp]
theorem complexIntegrateForm_re (σ : StokesF.SingularCubeStokes.SmoothSingularCube d m)
    (form : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin d]→L[ℝ] ℂ) :
    (complexIntegrateForm σ form).re = StokesF.SingularCubeStokes.integrateForm σ (OAI.Analysis.DifferentialForms.Manifold.Coefficients.Comparison.realForm form) := rfl

@[simp]
theorem complexIntegrateForm_im (σ : StokesF.SingularCubeStokes.SmoothSingularCube d m)
    (form : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin d]→L[ℝ] ℂ) :
    (complexIntegrateForm σ form).im = StokesF.SingularCubeStokes.integrateForm σ (OAI.Analysis.DifferentialForms.Manifold.Coefficients.Comparison.imagForm form) := rfl

/-- A smooth form has a continuous pullback coefficient. -/
theorem continuous_complexCubeIntegrand (σ : StokesF.SingularCubeStokes.SmoothSingularCube d m)
    (form : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin d]→L[ℝ] ℂ)
    (hform : ContDiff ℝ ∞ form) : Continuous (complexCubeIntegrand σ form) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ σ.toFun) :=
    σ.smooth.fderiv_right (by simp)
  have hp : Continuous (fun x =>
      (form (σ.toFun x)).compContinuousLinearMap (fderiv ℝ σ.toFun x)) :=
    (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp
      hfd.continuous).clm_apply (hform.continuous.comp σ.smooth.continuous)
  exact (ContinuousAlternatingMap.apply ℝ (Fin d → ℝ) ℂ
    (fun j : Fin d => Pi.single j 1)).continuous.comp hp

/-- Compactness of the unit cube gives integrability, without a new hypothesis. -/
theorem integrableOn_complexCubeIntegrand (σ : StokesF.SingularCubeStokes.SmoothSingularCube d m)
    (form : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin d]→L[ℝ] ℂ)
    (hform : ContDiff ℝ ∞ form) :
    IntegrableOn (complexCubeIntegrand σ form)
      (Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1)) :=
  (continuous_complexCubeIntegrand σ form hform).continuousOn.integrableOn_compact
    isCompact_Icc

/-- Componentwise integration equals the ordinary complex Bochner integral. -/
theorem complexIntegrateForm_eq_integral (σ : StokesF.SingularCubeStokes.SmoothSingularCube d m)
    (form : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin d]→L[ℝ] ℂ)
    (hform : ContDiff ℝ ∞ form) :
    complexIntegrateForm σ form =
      ∫ x in Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1),
        complexCubeIntegrand σ form x := by
  have hi := integrableOn_complexCubeIntegrand σ form hform
  apply Complex.ext
  · change (∫ x in Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1),
        (complexCubeIntegrand σ form x).re) = _
    exact integral_re hi
  · change (∫ x in Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1),
        (complexCubeIntegrand σ form x).im) = _
    exact integral_im hi

/-- Integration is additive on actual smooth complex forms. -/
theorem complexIntegrateForm_add (σ : StokesF.SingularCubeStokes.SmoothSingularCube d m)
    (form other : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin d]→L[ℝ] ℂ)
    (hform : ContDiff ℝ ∞ form) (hother : ContDiff ℝ ∞ other) :
    complexIntegrateForm σ (form + other) =
      complexIntegrateForm σ form + complexIntegrateForm σ other := by
  rw [complexIntegrateForm_eq_integral σ (form + other) (hform.add hother),
    complexIntegrateForm_eq_integral σ form hform,
    complexIntegrateForm_eq_integral σ other hother]
  change (∫ x in Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1),
    complexCubeIntegrand σ form x + complexCubeIntegrand σ other x) = _
  exact integral_add (integrableOn_complexCubeIntegrand σ form hform)
    (integrableOn_complexCubeIntegrand σ other hother)

/-- Complex scalars can be moved outside the integral of a smooth form. -/
theorem complexIntegrateForm_smul (σ : StokesF.SingularCubeStokes.SmoothSingularCube d m) (c : ℂ)
    (form : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin d]→L[ℝ] ℂ)
    (hform : ContDiff ℝ ∞ form) :
    complexIntegrateForm σ (c • form) = c • complexIntegrateForm σ form := by
  rw [complexIntegrateForm_eq_integral σ (c • form) (hform.const_smul c),
    complexIntegrateForm_eq_integral σ form hform]
  change (∫ x in Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1),
    c • complexCubeIntegrand σ form x) = _
  exact integral_smul c (complexCubeIntegrand σ form)

/-- Integration over a fixed smooth cube is a complex-linear functional on the
genuine space of smooth complex-valued differential forms. -/
def smoothComplexIntegration (σ : StokesF.SingularCubeStokes.SmoothSingularCube d m) :
    OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm (Fin m → ℝ) d →ₗ[ℂ] ℂ where
  toFun form := complexIntegrateForm σ form
  map_add' form other :=
    complexIntegrateForm_add σ form other form.smooth other.smooth
  map_smul' c form :=
    complexIntegrateForm_smul σ c form form.smooth

@[simp]
theorem smoothComplexIntegration_apply (σ : StokesF.SingularCubeStokes.SmoothSingularCube d m)
    (form : OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm (Fin m → ℝ) d) :
    smoothComplexIntegration σ form = complexIntegrateForm σ form := rfl

end

end OAI.AlgebraicTopology.DeRham.Comparison.ComplexCubeIntegration
