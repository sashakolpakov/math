import OAI.AlgebraicGeometry.DivisorClass.Chern.CauchyKernel
import OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-! # Cauchy Polar Calculus -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CauchyPolarCalculus

noncomputable section

/-! Actual scalar antiholomorphic derivatives and their polar-coordinate calculus. -/

open _root_.MeasureTheory _root_.Complex _root_.ContinuousLinearMap
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def complexDbar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM ℂ ℂ (fderiv ℝ f z) 1

theorem complexDbar_eq (f : ℂ → ℂ) (z : ℂ) :
    complexDbar f z = (1 / 2 : ℂ) * (fderiv ℝ f z 1 + I * fderiv ℝ f z I) := by
  simp only [complexDbar, Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply, smul_eq_mul, mul_one]

theorem complexDbar_continuous {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) :
    Continuous (complexDbar f) := by
  have hd := hf.continuous_fderiv (by simp)
  simp only [funext (complexDbar_eq f)]
  exact (hd.clm_apply continuous_const).add
    ((hd.clm_apply continuous_const).const_mul I) |>.const_mul (1 / 2 : ℂ)

theorem complexDbar_hasCompactSupport {f : ℂ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (complexDbar f) := by
  simp only [funext (complexDbar_eq f)]
  exact ((hf.fderiv_apply (𝕜 := ℝ) 1).add
    ((hf.fderiv_apply (𝕜 := ℝ) I).mul_left)).mul_left

def polarUnit (θ : ℝ) : ℂ := circleMap 0 1 θ

theorem polarUnit_norm (θ : ℝ) : ‖polarUnit θ‖ = 1 := by
  simp [polarUnit]

theorem polarUnit_ne_zero (θ : ℝ) : polarUnit θ ≠ 0 := by
  intro h
  have hn := polarUnit_norm θ
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

theorem polarCoord_eq (r θ : ℝ) : Complex.polarCoord.symm (r, θ) = r • polarUnit θ := by
  simp [Complex.polarCoord_symm_apply, polarUnit, circleMap, Complex.exp_mul_I,
    Complex.ofReal_cos, Complex.ofReal_sin, real_smul, mul_add]

theorem inv_mul_antilinear_eq (D : ℂ →L[ℝ] ℂ) (a : ℂ) (ha : ‖a‖ = 1) :
    a⁻¹ * Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM ℂ ℂ D 1 = (1 / 2 : ℂ) * (D a + I * D (I * a)) := by
  rw [Complex.inv_eq_conj ha]
  have h := Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply_smul ℂ ℂ D a (1 : ℂ)
  simpa only [Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply, smul_eq_mul, mul_one, Complex.star_def] using h.symm

theorem complexDbar_polar (f : ℂ → ℂ) {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    r • ((Complex.polarCoord.symm (r, θ))⁻¹ * complexDbar f (Complex.polarCoord.symm (r, θ))) =
      (1 / 2 : ℂ) *
        (fderiv ℝ f (r • polarUnit θ) (polarUnit θ) +
          I * fderiv ℝ f (r • polarUnit θ) (I * polarUnit θ)) := by
  rw [polarCoord_eq]
  change (r : ℂ) * (((r : ℂ) * polarUnit θ)⁻¹ * complexDbar f (r • polarUnit θ)) = _
  rw [mul_inv_rev]
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  calc
    (r : ℂ) * ((polarUnit θ)⁻¹ * (r : ℂ)⁻¹ * complexDbar f (r • polarUnit θ)) =
        (polarUnit θ)⁻¹ * complexDbar f (r • polarUnit θ) := by field_simp
    _ = _ := inv_mul_antilinear_eq _ _ (polarUnit_norm θ)

theorem polarRadial_hasDerivAt {f : ℂ → ℂ} (hf : Differentiable ℝ f) (r θ : ℝ) :
    HasDerivAt (fun s : ℝ => f (s • polarUnit θ))
      (fderiv ℝ f (r • polarUnit θ) (polarUnit θ)) r := by
  simpa only [one_smul, Function.comp_def, id_eq] using! (hf (r • polarUnit θ)).hasFDerivAt.comp_hasDerivAt r
    ((hasDerivAt_id r).smul_const (polarUnit θ))

theorem polarAngular_hasDerivAt {f : ℂ → ℂ} (hf : Differentiable ℝ f) (r θ : ℝ) :
    HasDerivAt (fun t : ℝ => f (r • polarUnit t))
      (r • fderiv ℝ f (r • polarUnit θ) (I * polarUnit θ)) θ := by
  have hunit : HasDerivAt polarUnit (I * polarUnit θ) θ := by
    change HasDerivAt (circleMap 0 1) (I * circleMap 0 1 θ) θ
    simpa only [mul_comm] using hasDerivAt_circleMap 0 1 θ
  simpa only [map_smul, Function.comp_def, Pi.smul_apply] using! (hf (r • polarUnit θ)).hasFDerivAt.comp_hasDerivAt θ
    (hunit.const_smul r)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CauchyPolarCalculus
