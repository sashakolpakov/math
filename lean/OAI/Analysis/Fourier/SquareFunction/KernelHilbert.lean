import OAI.Analysis.Fourier.SquareFunction.Radius.Hilbert
import OAI.Analysis.Fourier.SquareFunction.ConvolutionRegularity

open OAI.Analysis.Fourier.Wave

/-! Compact frequency symbols with continuous radius dependence define
genuine differentiable Hilbert-valued inverse Fourier kernels. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform

theorem integrable_spatialPhase_smul {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (x : Space n)
    {a : Space n → E} (ha : Integrable a) :
    Integrable (fun ξ => spatialPhase x ξ • a ξ) := by
  have hmeas : AEStronglyMeasurable (fun ξ => spatialPhase x ξ • a ξ) volume :=
    (continuous_spatialPhase x).aestronglyMeasurable.smul ha.aestronglyMeasurable
  have hn (ξ : Space n) : ‖spatialPhase x ξ • a ξ‖ ≤ ‖a ξ‖ := by
    rw [norm_smul, norm_spatialPhase, one_mul]
  exact ha.mono hmeas (Filter.Eventually.of_forall hn)

theorem fourierInv_eq_spatialPhase_smul {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (a : Space n → E) (x : Space n) :
    𝓕⁻ a x = ∫ ξ, spatialPhase x ξ • a ξ := by
  rw [Real.fourierInv_eq']
  rfl

theorem fourierInv_continuousMap_apply {n : ℕ}
    {m : Space n → C(RadiusInterval, ℂ)} (hm : Integrable m)
    (x : Space n) (r : RadiusInterval) :
    (𝓕⁻ m x) r = 𝓕⁻ (fun ξ => m ξ r) x := by
  rw [fourierInv_eq_spatialPhase_smul, fourierInv_eq_spatialPhase_smul,
    ContinuousMap.integral_apply (integrable_spatialPhase_smul x hm)]
  rfl

noncomputable def radiusFourierKernel {n : ℕ} (m : Space n → C(RadiusInterval, ℂ))
    (x : Space n) : RadiusHilbert := radiusToL2 (𝓕⁻ m x)

theorem radiusFourierKernel_coe {n : ℕ} {m : Space n → C(RadiusInterval, ℂ)}
    (hm : Integrable m) (x : Space n) :
    (radiusFourierKernel m x : RadiusInterval → ℂ) =ᵐ[radiusMeasure]
      (fun r => 𝓕⁻ (fun ξ => m ξ r) x) := by
  filter_upwards [radiusToL2_coe (𝓕⁻ m x)] with r hr
  exact hr.trans (fourierInv_continuousMap_apply hm x r)

theorem differentiable_fourierInv_compact {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {m : Space n → E} (hm : Continuous m) (hc : HasCompactSupport m) :
    Differentiable ℝ (𝓕⁻ m) := by
  have hi : Integrable m := hm.integrable_of_hasCompactSupport hc
  have hw : Integrable (fun ξ => ‖ξ‖ * ‖m ξ‖) :=
    (continuous_norm.mul hm.norm).integrable_of_hasCompactSupport hc.norm.mul_left
  have hn : Differentiable ℝ (fun x : Space n => -x) := differentiable_id.neg
  have h := (Real.differentiable_fourier hi hw).comp hn
  have he : 𝓕⁻ m = fun x => 𝓕 m (-x) := funext (Real.fourierInv_eq_fourier_neg m)
  rw [he]
  exact h

theorem differentiable_radiusFourierKernel {n : ℕ}
    {m : Space n → C(RadiusInterval, ℂ)} (hm : Continuous m) (hc : HasCompactSupport m) :
    Differentiable ℝ (radiusFourierKernel m) :=
  (radiusToL2.restrictScalars ℝ).differentiable.comp (differentiable_fourierInv_compact hm hc)

theorem norm_radiusFourierKernel_le {n : ℕ} {m : Space n → C(RadiusInterval, ℂ)}
    (hm : Integrable m) (x : Space n) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ r : RadiusInterval, ‖𝓕⁻ (fun ξ => m ξ r) x‖ ≤ B) :
    ‖radiusFourierKernel m x‖ ≤ B := by
  apply (norm_radiusToL2_le _).trans
  apply (ContinuousMap.norm_le _ hB).2
  intro r
  rw [fourierInv_continuousMap_apply hm x r]
  exact hbound r

end OAI.Analysis.Fourier.SquareFunction
