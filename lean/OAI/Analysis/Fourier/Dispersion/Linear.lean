import OAI.Analysis.Fourier.Dispersion.LinearNorm

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.Dispersion

open _root_.MeasureTheory
open scoped ENNReal

/-- Fourier multipliers are conjugated by the transpose spatial map.  Both
Jacobian factors cancel before any estimate is taken. -/
theorem angularMultiplier_comp_linearEquiv {n : ℕ}
    (R : Space n ≃L[ℝ] Space n) (m f : Space n → ℂ) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ => m ξ * OAI.Analysis.Fourier.LocalSmoothing.angularFourier (f ∘ adjointEquiv R) ξ) x =
      OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ => m (R ξ) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ) (adjointEquiv R x) := by
  let g : Space n → ℂ := fun ξ => m (R ξ) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ
  let d := LinearMap.det R.toLinearEquiv.toLinearMap
  have hd : d ≠ 0 := R.toLinearEquiv.isUnit_det'.ne_zero
  have hdet : LinearMap.det (adjointEquiv R).toLinearEquiv.toLinearMap = d :=
    OAI.Analysis.Fourier.WavePackets.det_adjoint_real R.toLinearEquiv.toLinearMap
  have hdetInv : LinearMap.det R.symm.toLinearEquiv.toLinearMap = d⁻¹ :=
    R.toLinearEquiv.det_coe_symm
  have heq : (fun ξ => m ξ * OAI.Analysis.Fourier.LocalSmoothing.angularFourier (f ∘ adjointEquiv R) ξ) =
      fun ξ => |d⁻¹| • (g ∘ R.symm) ξ := by
    funext ξ
    rw [angularFourier_comp_linearEquiv,hdet,adjointEquiv_symm,adjointEquiv_adjointEquiv]
    simp only [Function.comp_apply,g,R.apply_symm_apply,mul_smul_comm]
  rw [heq,OAI.Analysis.Fourier.BochnerRiesz.angularInverse_smul_real,angularInverse_comp_linearEquiv]
  simp only [ContinuousLinearEquiv.symm_symm,hdetInv,smul_smul]
  change (|d⁻¹| * |(d⁻¹)⁻¹|) • OAI.Analysis.Fourier.LocalSmoothing.angularInverse g (adjointEquiv R x) = _
  rw [← abs_mul,inv_inv,inv_mul_cancel₀ hd,abs_one,one_smul]

theorem frequencyDispersion_comp_linearEquiv {n : ℕ}
    (R : Space n ≃L[ℝ] Space n) (disp : Space n → ℝ) (φ : Space n → ℂ)
    (h t : ℝ) (f : Space n → ℂ) (x : Space n) :
    frequencyDispersion disp φ h t (f ∘ adjointEquiv R) x =
      frequencyDispersion (disp ∘ R) (φ ∘ R) h t f (adjointEquiv R x) := by
  simpa only [frequencyDispersion,Function.comp_apply,map_smul] using
    angularMultiplier_comp_linearEquiv R
      (fun ξ => Complex.exp (-Complex.I*(t*disp ξ:ℝ))*φ (h•ξ)) f x

/-- A frequency-localized spacetime estimate transfers to every invertible
linear frequency change with precisely the same constant. -/
theorem frequencyDispersion_bound_comp_linearEquiv {n : ℕ}
    (R : Space n ≃L[ℝ] Space n) (disp : Space n → ℝ) (φ : Space n → ℂ)
    (h : ℝ) (p B : ℝ≥0∞)
    (hbound : ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ => frequencyDispersion disp φ h z.2 f z.1)
        p (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤ B * eLpNorm f p volume) :
    ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ => frequencyDispersion (disp ∘ R) (φ ∘ R) h z.2 f z.1)
        p (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤ B * eLpNorm f p volume := by
  intro f
  let A := adjointEquiv R
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A f
  have hg : (g : Space n → ℂ) = (f : Space n → ℂ) ∘ A := rfl
  have hb := hbound g
  rw [hg,eLpNorm_comp_linearEquiv] at hb
  have heq : (fun z : Space n × ℝ => frequencyDispersion disp φ h z.2 ((f : Space n → ℂ) ∘ A) z.1) =
      fun z : Space n × ℝ => frequencyDispersion (disp ∘ R) (φ ∘ R) h z.2 f (A z.1) := by
    funext z
    exact frequencyDispersion_comp_linearEquiv R disp φ h z.2 f z.1
  rw [heq,eLpNorm_observation_comp_linearEquiv A
    (fun z : Space n × ℝ => frequencyDispersion (disp ∘ R) (φ ∘ R) h z.2 f z.1) p] at hb
  have hc0 : (linearJacobian A) ^ (1/p).toReal ≠ 0 :=
    ne_of_gt (ENNReal.rpow_pos (pos_iff_ne_zero.mpr (linearJacobian_ne_zero A))
      (linearJacobian_ne_top A))
  have hct : (linearJacobian A) ^ (1/p).toReal ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero (linearJacobian_ne_zero A) (linearJacobian_ne_top A)
  rw [← mul_assoc,mul_comm B, mul_assoc] at hb
  have hcancel := mul_le_mul' (le_refl (((linearJacobian A) ^ (1/p).toReal)⁻¹)) hb
  simpa only [← mul_assoc,ENNReal.inv_mul_cancel hc0 hct,one_mul] using hcancel

end OAI.Analysis.Fourier.Dispersion
