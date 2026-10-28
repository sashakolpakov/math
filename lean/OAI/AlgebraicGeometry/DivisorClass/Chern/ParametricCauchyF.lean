import OAI.AlgebraicGeometry.DivisorClass.Chern.CauchyPolarIntegral

/-! # Parametric Cauchy F -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ParametricCauchyF

noncomputable section

section

/-! Actual Cauchy primitives depending smoothly on parameters on an open domain. -/

open _root_.MeasureTheory _root_.Complex Set
open scoped ContDiff Convolution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def parametricCauchyTransform (g : P → ℂ → ℂ) (q : P × ℂ) : ℂ := CauchyKernel.cauchyTransform (g q.1) q.2

theorem parametricCauchyTransform_smooth {g : P → ℂ → ℂ} {S : Set P} {K : Set ℂ}
    (hS : IsOpen S) (hK : IsCompact K)
    (hsupp : ∀ p w, p ∈ S → w ∉ K → g p w = 0)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ univ)) :
    ContDiffOn ℝ ∞ (parametricCauchyTransform g) (S ×ˢ univ) :=
  contDiffOn_convolution_right_with_param (ContinuousLinearMap.mul ℝ ℂ)
    hS hK hsupp CauchyKernel.cauchyKernel_locallyIntegrable hg

theorem parametricCauchyTransform_slice_primitive {g : P → ℂ → ℂ} {S : Set P} {K : Set ℂ}
    (hK : IsCompact K) (hsupp : ∀ p w, p ∈ S → w ∉ K → g p w = 0)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ univ)) {p : P} (hp : p ∈ S) (z : ℂ) :
    CauchyPolarCalculus.complexDbar (fun w => parametricCauchyTransform g (p, w)) z = g p z := by
  have hcompact : HasCompactSupport (g p) :=
    exists_compact_iff_hasCompactSupport.mp ⟨K, hK, fun w hw => hsupp p w hp hw⟩
  have hsmooth : ContDiff ℝ ∞ (g p) := by
    rw [← contDiffOn_univ]
    exact hg.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => ⟨hp, mem_univ _⟩)
  exact CauchyPolarIntegral.complexDbar_cauchyTransform hsmooth hcompact z

theorem parametricCauchyTransform_hasFDerivAt {g : P → ℂ → ℂ} {S : Set P} {K : Set ℂ}
    (hS : IsOpen S) (hK : IsCompact K)
    (hsupp : ∀ p w, p ∈ S → w ∉ K → g p w = 0)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ univ))
    (q : P × ℂ) (hq : q.1 ∈ S) :
    HasFDerivAt (parametricCauchyTransform g)
      ((CauchyKernel.cauchyKernel ⋆[(ContinuousLinearMap.mul ℝ ℂ).precompR (P × ℂ), volume]
        fun w : ℂ => fderiv ℝ (Function.uncurry g) (q.1, w)) q.2) q :=
  hasFDerivAt_convolution_right_with_param (ContinuousLinearMap.mul ℝ ℂ)
    hS hK hsupp CauchyKernel.cauchyKernel_locallyIntegrable (hg.of_le (by simp)) q hq

end

section

/-! Differentiating the actual parameter-dependent Cauchy integral. -/

open _root_.MeasureTheory _root_.Complex Set Filter
open scoped ContDiff Convolution _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem parametricDerivativeSlice_hasCompactSupport {g : P → ℂ → ℂ} {S : Set P} {K : Set ℂ}
    (hS : IsOpen S) (hK : IsCompact K)
    (hsupp : ∀ p w, p ∈ S → w ∉ K → g p w = 0) {p : P} (hp : p ∈ S) :
    HasCompactSupport (fun w : ℂ => fderiv ℝ (Function.uncurry g) (p, w)) := by
  apply exists_compact_iff_hasCompactSupport.mp
  refine ⟨K, hK, fun w hw => ?_⟩
  have he : Function.uncurry g =ᶠ[𝓝 (p, w)] 0 := by
    filter_upwards [(hS.prod hK.isClosed.isOpen_compl).mem_nhds ⟨hp, hw⟩] with q hq
    exact hsupp q.1 q.2 hq.1 hq.2
  rw [he.fderiv_eq]
  exact (hasFDerivAt_const (0 : ℂ) (p, w)).fderiv

theorem parametricDerivativeSlice_continuous {g : P → ℂ → ℂ} {S : Set P}
    (hS : IsOpen S) (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ univ))
    {p : P} (hp : p ∈ S) :
    Continuous (fun w : ℂ => fderiv ℝ (Function.uncurry g) (p, w)) := by
  have hd := hg.fderiv_of_isOpen (hS.prod isOpen_univ) (m := ∞) (by simp)
  have hs : ContDiffOn ℝ ∞ (fun w : ℂ => fderiv ℝ (Function.uncurry g) (p, w)) univ :=
    hd.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => ⟨hp, mem_univ _⟩)
  exact (contDiffOn_univ.mp hs).continuous

theorem parametricCauchyTransform_fderiv_apply {g : P → ℂ → ℂ} {S : Set P} {K : Set ℂ}
    (hS : IsOpen S) (hK : IsCompact K)
    (hsupp : ∀ p w, p ∈ S → w ∉ K → g p w = 0)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ univ))
    (q : P × ℂ) (hq : q.1 ∈ S) (v : P × ℂ) :
    fderiv ℝ (parametricCauchyTransform g) q v =
      ∫ w : ℂ, CauchyKernel.cauchyKernel w * fderiv ℝ (Function.uncurry g) (q.1, q.2 - w) v := by
  rw [(parametricCauchyTransform_hasFDerivAt hS hK hsupp hg q hq).fderiv]
  have hi := (parametricDerivativeSlice_hasCompactSupport hS hK hsupp hq).convolutionExists_right
    ((ContinuousLinearMap.mul ℝ ℂ).precompR (P × ℂ)) CauchyKernel.cauchyKernel_locallyIntegrable
    (parametricDerivativeSlice_continuous hS hg hq) q.2
  exact ContinuousLinearMap.integral_apply hi.integrable v

variable [NormedSpace ℂ P]

theorem parametricCauchyTransform_preserves_holomorphic_direction
    {g : P → ℂ → ℂ} {S : Set P} {K : Set ℂ}
    (hS : IsOpen S) (hK : IsCompact K)
    (hsupp : ∀ p w, p ∈ S → w ∉ K → g p w = 0)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ univ))
    (q : P × ℂ) (hq : q.1 ∈ S) (v : P)
    (hv : ∀ w : ℂ, fderiv ℝ (Function.uncurry g) (q.1, w) (I • v, 0) =
      I * fderiv ℝ (Function.uncurry g) (q.1, w) (v, 0)) :
    fderiv ℝ (parametricCauchyTransform g) q (I • v, 0) =
      I * fderiv ℝ (parametricCauchyTransform g) q (v, 0) := by
  rw [parametricCauchyTransform_fderiv_apply hS hK hsupp hg q hq,
    parametricCauchyTransform_fderiv_apply hS hK hsupp hg q hq, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with w
  rw [hv]
  ring

end

/-! Smooth cutoffs in the integration variable, preserving parameter derivatives. -/

open _root_.MeasureTheory _root_.Complex Set Filter
open scoped ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def cutoffCauchyInput (χ : ℂ → ℝ) (g : P → ℂ → ℂ) (p : P) (w : ℂ) : ℂ := χ w • g p w

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem cutoffCauchyInput_support (χ : ℂ → ℝ) (g : P → ℂ → ℂ) (p : P) (w : ℂ)
    (hw : w ∉ tsupport χ) : cutoffCauchyInput χ g p w = 0 := by
  unfold cutoffCauchyInput
  rw [image_eq_zero_of_notMem_tsupport hw, zero_smul]

theorem cutoffCauchyInput_smooth {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {g : P → ℂ → ℂ} {S : Set P} {U : Set ℂ} (hS : IsOpen S) (hU : IsOpen U)
    (hsub : tsupport χ ⊆ U) (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ U)) :
    ContDiffOn ℝ ∞ (Function.uncurry (cutoffCauchyInput χ g)) (S ×ˢ univ) := by
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  by_cases hw : q.2 ∈ tsupport χ
  · exact (hχ.comp contDiff_snd).contDiffAt.smul
      (hg.contDiffAt ((hS.prod hU).mem_nhds ⟨hq.1, hsub hw⟩))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hw).comp_tendsto
      continuous_snd.continuousAt] with r hr
    change χ r.2 • g r.1 r.2 = 0
    rw [show χ r.2 = 0 from hr, zero_smul]

theorem cutoffCauchyInput_parameterDerivative {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {g : P → ℂ → ℂ} {S : Set P} {U : Set ℂ} (hS : IsOpen S) (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ U))
    {p : P} (hp : p ∈ S) {w : ℂ} (hw : w ∈ U) (v : P) :
    fderiv ℝ (Function.uncurry (cutoffCauchyInput χ g)) (p, w) (v, 0) =
      χ w • fderiv ℝ (Function.uncurry g) (p, w) (v, 0) := by
  have hcoeff := (hχ.differentiable (by simp) w).hasFDerivAt.comp (p, w) (hasFDerivAt_snd (𝕜 := ℝ) (p := (p, w)))
  have hinput : DifferentiableAt ℝ (Function.uncurry g) (p, w) :=
    (hg.contDiffAt ((hS.prod hU).mem_nhds ⟨hp, hw⟩)).differentiableAt (by simp)
  have hd := congrArg (fun D : (P × ℂ) →L[ℝ] ℂ => D (v, 0)) (hcoeff.smul hinput.hasFDerivAt).fderiv
  change fderiv ℝ (Function.uncurry (cutoffCauchyInput χ g)) (p, w) (v, 0) =
    χ w • fderiv ℝ (Function.uncurry g) (p, w) (v, 0) +
      fderiv ℝ χ w 0 • g p w at hd
  simpa only [map_zero, zero_smul, add_zero] using hd

theorem cutoffCauchyInput_fderiv_zero {χ : ℂ → ℝ} {g : P → ℂ → ℂ}
    {p : P} {w : ℂ} (hw : w ∉ tsupport χ) :
    fderiv ℝ (Function.uncurry (cutoffCauchyInput χ g)) (p, w) = 0 := by
  have he : Function.uncurry (cutoffCauchyInput χ g) =ᶠ[𝓝 (p, w)] 0 := by
    filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hw).comp_tendsto
      continuous_snd.continuousAt] with q hq
    change χ q.2 • g q.1 q.2 = 0
    rw [show χ q.2 = 0 from hq, zero_smul]
  rw [he.fderiv_eq]
  exact (hasFDerivAt_const (0 : ℂ) (p, w)).fderiv

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ParametricCauchyF
