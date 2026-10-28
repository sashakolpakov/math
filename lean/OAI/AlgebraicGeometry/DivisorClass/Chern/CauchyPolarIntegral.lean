import OAI.AlgebraicGeometry.DivisorClass.Chern.CauchyPolarIntegrals
import Mathlib.MeasureTheory.Integral.Prod

/-! # Cauchy Polar Integral -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CauchyPolarIntegral

noncomputable section

section

/-! Integration of the actual antiholomorphic derivative in a bounded polar rectangle. -/

open _root_.MeasureTheory _root_.Complex Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def polarDbarDensity (f : ℂ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f (p.1 • CauchyPolarCalculus.polarUnit p.2) (CauchyPolarCalculus.polarUnit p.2) +
    I * fderiv ℝ f (p.1 • CauchyPolarCalculus.polarUnit p.2) (I * CauchyPolarCalculus.polarUnit p.2))

theorem polarDbarDensity_continuous {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) :
    Continuous (polarDbarDensity f) :=
  ((CauchyPolarIntegrals.polarRadialDerivative_continuous hf).add
    ((CauchyPolarIntegrals.polarAngularDerivative_continuous hf).const_mul I)).const_mul (1 / 2 : ℂ)

theorem integral_polarDbarDensity_angular {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    {r : ℝ} (hr : r ≠ 0) :
    (∫ θ in (-Real.pi)..Real.pi, polarDbarDensity f (r, θ)) =
      (1 / 2 : ℂ) * ∫ θ in (-Real.pi)..Real.pi,
        fderiv ℝ f (r • CauchyPolarCalculus.polarUnit θ) (CauchyPolarCalculus.polarUnit θ) := by
  have hrad : Continuous (fun θ : ℝ => fderiv ℝ f (r • CauchyPolarCalculus.polarUnit θ) (CauchyPolarCalculus.polarUnit θ)) :=
    (CauchyPolarIntegrals.polarRadialDerivative_continuous hf).comp (continuous_const.prodMk continuous_id)
  have hang : Continuous (fun θ : ℝ => fderiv ℝ f (r • CauchyPolarCalculus.polarUnit θ) (I * CauchyPolarCalculus.polarUnit θ)) :=
    (CauchyPolarIntegrals.polarAngularDerivative_continuous hf).comp (continuous_const.prodMk continuous_id)
  simp only [polarDbarDensity, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_add (hrad.intervalIntegrable _ _)
    ((hang.const_mul I).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    CauchyPolarIntegrals.integral_polarAngularDerivative hf hr, mul_zero, add_zero]

theorem integral_polarDbarDensity {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (R : ℝ)
    (hR : ∀ θ : ℝ, f (R • CauchyPolarCalculus.polarUnit θ) = 0) :
    (∫ r in (0 : ℝ)..R, ∫ θ in (-Real.pi)..Real.pi, polarDbarDensity f (r, θ)) =
      -(Real.pi : ℂ) * f 0 := by
  have hfirst :
      (∫ r in (0 : ℝ)..R, ∫ θ in (-Real.pi)..Real.pi, polarDbarDensity f (r, θ)) =
        (∫ r in (0 : ℝ)..R, (1 / 2 : ℂ) * ∫ θ in (-Real.pi)..Real.pi,
          fderiv ℝ f (r • CauchyPolarCalculus.polarUnit θ) (CauchyPolarCalculus.polarUnit θ)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (0 : ℝ)] with r hr
    intro _
    exact integral_polarDbarDensity_angular hf hr
  rw [hfirst, intervalIntegral.integral_const_mul]
  have hi : IntegrableOn
      (fun p : ℝ × ℝ => fderiv ℝ f (p.1 • CauchyPolarCalculus.polarUnit p.2) (CauchyPolarCalculus.polarUnit p.2))
      (uIoc 0 R ×ˢ uIoc (-Real.pi) Real.pi) :=
    ((CauchyPolarIntegrals.polarRadialDerivative_continuous hf).continuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_uIcc)).mono_set (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  rw [intervalIntegral_intervalIntegral_swap
    (F := fun r θ => fderiv ℝ f (r • CauchyPolarCalculus.polarUnit θ) (CauchyPolarCalculus.polarUnit θ)) hi]
  simp_rw [CauchyPolarIntegrals.integral_polarRadialDerivative hf, hR, zero_sub]
  rw [intervalIntegral.integral_const]
  simp only [sub_neg_eq_add, real_smul, Complex.ofReal_add]
  ring

end

section

/-! The distributional Cauchy-kernel identity, proved by genuine polar integration. -/

open _root_.MeasureTheory _root_.Complex Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem compactSupport_complex_radius {f : ℂ → ℂ} (hc : HasCompactSupport f) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ → f z = 0 ∧ fderiv ℝ f z = 0 := by
  obtain ⟨R, hR, hbound⟩ := hc.isCompact.isBounded.exists_pos_norm_lt
  refine ⟨R, hR, fun z hz => ?_⟩
  have hout : z ∉ tsupport f := fun h => (not_lt_of_ge hz) (hbound z h)
  exact ⟨image_eq_zero_of_notMem_tsupport hout, fderiv_of_notMem_tsupport ℝ hout⟩

theorem integral_inv_mul_complexDbar {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    (∫ z : ℂ, z⁻¹ * CauchyPolarCalculus.complexDbar f z) = -(Real.pi : ℂ) * f 0 := by
  obtain ⟨R, hR, hbound⟩ := compactSupport_complex_radius hc
  rw [← Complex.integral_comp_polarCoord_symm]
  have heq :
      (∫ p in polarCoord.target, p.1 •
        ((Complex.polarCoord.symm p)⁻¹ * CauchyPolarCalculus.complexDbar f (Complex.polarCoord.symm p))) =
        ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, polarDbarDensity f p := by
    apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    exact CauchyPolarCalculus.complexDbar_polar f (ne_of_gt hp.1) p.2
  rw [heq]
  have hcut :
      (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, polarDbarDensity f p) =
        ∫ p in Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi, polarDbarDensity f p := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (measurableSet_Ioi.prod measurableSet_Ioo) (prod_mono Ioo_subset_Ioi_self Subset.rfl)
    intro p hp
    have hlarge : R ≤ p.1 := by
      by_contra! h
      exact hp.2 ⟨⟨hp.1.1, h⟩, hp.1.2⟩
    have hn : ‖p.1 • CauchyPolarCalculus.polarUnit p.2‖ = p.1 := by
      rw [norm_smul, Real.norm_eq_abs, CauchyPolarCalculus.polarUnit_norm, mul_one, abs_of_pos hp.1.1]
    have hd := (hbound (p.1 • CauchyPolarCalculus.polarUnit p.2) (by rwa [hn])).2
    unfold polarDbarDensity
    rw [hd]
    simp
  rw [hcut]
  have hi : IntegrableOn (polarDbarDensity f)
      (Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact ((polarDbarDensity_continuous hf).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
        (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  rw [Measure.volume_eq_prod, setIntegral_prod _ hi]
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  simp_rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hR.le, ← intervalIntegral.integral_of_le hpi]
  apply integral_polarDbarDensity hf R
  intro θ
  apply (hbound (R • CauchyPolarCalculus.polarUnit θ) _).1
  rw [norm_smul, Real.norm_eq_abs, CauchyPolarCalculus.polarUnit_norm, mul_one, abs_of_pos hR]

end

section

/-! Translation and normalization of the genuine Cauchy-kernel identity. -/

open _root_.MeasureTheory _root_.Complex
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem complexDbar_sub_left {f : ℂ → ℂ} (hf : Differentiable ℝ f) (z w : ℂ) :
    CauchyPolarCalculus.complexDbar (fun v => f (z - v)) w = -CauchyPolarCalculus.complexDbar f (z - w) := by
  have hd : fderiv ℝ (fun v => f (z - v)) w = -fderiv ℝ f (z - w) := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.comp_zero, ContinuousLinearMap.comp_id, zero_sub,
      ContinuousLinearMap.comp_neg] using!
      ((hf (z - w)).hasFDerivAt.comp w
        ((hasFDerivAt_const z w).sub (hasFDerivAt_id w))).fderiv
  unfold CauchyPolarCalculus.complexDbar
  rw [hd, map_neg]
  rfl

theorem integral_cauchyKernel_mul_complexDbar {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (z : ℂ) :
    (∫ w : ℂ, CauchyKernel.cauchyKernel w * CauchyPolarCalculus.complexDbar f (z - w)) = f z := by
  have hr := integral_inv_mul_complexDbar (f := fun w => f (z - w))
    (hf.comp (contDiff_const.sub contDiff_id)) (hc.comp_homeomorph (Homeomorph.subLeft z))
  simp_rw [complexDbar_sub_left (hf.differentiable (by simp)), mul_neg] at hr
  rw [integral_neg] at hr
  simp only [sub_zero, neg_mul] at hr
  have hraw : (∫ w : ℂ, w⁻¹ * CauchyPolarCalculus.complexDbar f (z - w)) = (Real.pi : ℂ) * f z := neg_injective hr
  simp only [CauchyKernel.cauchyKernel, mul_assoc, integral_const_mul]
  rw [hraw, ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero), one_mul]

end

/-! The actual Cauchy transform is a right inverse to the antiholomorphic scalar derivative. -/

open _root_.MeasureTheory _root_.Complex _root_.ContinuousLinearMap
open scoped ContDiff Convolution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def scalarDbarDerivativeCLM : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).comp
    ((Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM ℂ ℂ).restrictScalars ℝ)

theorem scalarDbarDerivativeCLM_smul (c : ℂ) (D : ℂ →L[ℝ] ℂ) :
    scalarDbarDerivativeCLM (c • D) = c * scalarDbarDerivativeCLM D := by
  change Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM ℂ ℂ (c • D) 1 = c * Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM ℂ ℂ D 1
  rw [map_smul]
  rfl

theorem complexDbar_cauchyTransform_integral {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (z : ℂ) :
    CauchyPolarCalculus.complexDbar (CauchyKernel.cauchyTransform f) z =
      ∫ w : ℂ, CauchyKernel.cauchyKernel w * CauchyPolarCalculus.complexDbar f (z - w) := by
  have hd := (CauchyKernel.cauchyTransform_hasFDerivAt hc (hf.of_le (by simp)) z).fderiv
  have hi := (hc.fderiv ℝ).convolutionExists_right
    ((ContinuousLinearMap.mul ℝ ℂ).precompR ℂ) CauchyKernel.cauchyKernel_locallyIntegrable
    (hf.continuous_fderiv (by simp)) z
  unfold CauchyPolarCalculus.complexDbar
  rw [hd]
  change scalarDbarDerivativeCLM
    (∫ w : ℂ, ((ContinuousLinearMap.mul ℝ ℂ).precompR ℂ)
      (CauchyKernel.cauchyKernel w) (fderiv ℝ f (z - w))) = _
  rw [← scalarDbarDerivativeCLM.integral_comp_comm hi.integrable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w => scalarDbarDerivativeCLM_smul (CauchyKernel.cauchyKernel w) _)

theorem complexDbar_cauchyTransform {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (z : ℂ) : CauchyPolarCalculus.complexDbar (CauchyKernel.cauchyTransform f) z = f z := by
  rw [complexDbar_cauchyTransform_integral hf hc, integral_cauchyKernel_mul_complexDbar hf hc]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CauchyPolarIntegral
