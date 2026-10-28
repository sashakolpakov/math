import OAI.Analysis.Fourier.SquareFunction.SmoothRadiusKernel
import OAI.Analysis.Fourier.SquareFunction.ClassicalPlancherel
import OAI.Analysis.Fourier.SquareFunction.Shell.OperatorBounds

open OAI.Analysis.Fourier.Wave

/-! Plancherel for the actual compact smooth radius-dependent symbol. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform Set
open scoped ENNReal

theorem hasCompactSupport_radius_slice {n : ℕ} {A : ℝ × Space n → ℂ}
    (hc : HasCompactSupport A) (r : ℝ) :
    HasCompactSupport (fun ξ : Space n => A (r, ξ)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hc.image continuous_snd)
  exact fun ξ hξ => ⟨(r, ξ), subset_tsupport A hξ, rfl⟩

theorem measurable_fourierInv_family {n : ℕ} {m : ℝ × Space n → ℂ}
    (hm : Measurable m) :
    Measurable (fun z : ℝ × Space n => 𝓕⁻ (fun ξ : Space n => m (z.1, ξ)) z.2) := by
  have hi : StronglyMeasurable (fun z : (ℝ × Space n) × Space n =>
      spatialPhase z.1.2 z.2 * m (z.1.1, z.2)) := by
    apply Measurable.stronglyMeasurable
    have hm' : Measurable (fun z : (ℝ × Space n) × Space n => m (z.1.1, z.2)) :=
      hm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    unfold spatialPhase
    fun_prop
  simpa only [fourierInv_eq_spatialPhase_smul, smul_eq_mul] using
    (hi.integral_prod_right' (ν := (volume : Measure (Space n)))).measurable

theorem enorm_smoothRadiusOutput {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (hc : HasCompactSupport A) {f : Space n → ℂ}
    (hf : Integrable f) (x : Space n) :
    ‖radiusToL2 (smoothRadiusOutput A hA f x)‖ₑ =
      eLpNorm (fun r : ℝ => 𝓕⁻ (fun ξ : Space n => A (r, ξ) * 𝓕 f ξ) x)
        2 (volume.restrict (Icc (1 : ℝ) 2)) := by
  rw [enorm_radiusToL2]
  have he := funext (smoothRadiusOutput_apply A hA hc hf x)
  rw [he]
  exact eLpNorm_radius_restriction (fun r : ℝ =>
    𝓕⁻ (fun ξ : Space n => A (r, ξ) * 𝓕 f ξ) x) 2

theorem smoothRadiusOutput_energy {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (hc : HasCompactSupport A) {f : Space n → ℂ}
    (hf : Integrable f) :
    (∫⁻ x : Space n, ‖radiusToL2 (smoothRadiusOutput A hA f x)‖ₑ ^ (2 : ℝ)) =
      ∫⁻ ξ : Space n, (∫⁻ r in Icc (1 : ℝ) 2, ‖A (r, ξ)‖ₑ ^ (2 : ℝ)) *
        ‖𝓕 f ξ‖ₑ ^ (2 : ℝ) := by
  let m : ℝ × Space n → ℂ := fun z => A z * 𝓕 f z.2
  have hm : Continuous m := hA.mul ((OAI.Analysis.Fourier.BochnerRiesz.continuous_fourier_of_integrable hf).comp continuous_snd)
  have hmc (r : ℝ) : HasCompactSupport (fun ξ : Space n => m (r, ξ)) :=
    (hasCompactSupport_radius_slice hc r).mul_right
  have hmr (r : ℝ) : Continuous (fun ξ : Space n => m (r, ξ)) :=
    hm.comp (continuous_const.prodMk continuous_id)
  have ho := measurable_fourierInv_family (n := n) hm.measurable
  have hs (x : Space n) : ‖radiusToL2 (smoothRadiusOutput A hA f x)‖ₑ ^ (2 : ℝ) =
      ∫⁻ r in Icc (1 : ℝ) 2, ‖𝓕⁻ (fun ξ : Space n => m (r, ξ)) x‖ₑ ^ (2 : ℝ) := by
    rw [enorm_smoothRadiusOutput A hA hc hf x]
    exact eLpNorm_two_rpow_general _ (ho.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  simp_rw [hs]
  rw [lintegral_lintegral_swap ((ho.comp measurable_swap).enorm.pow_const (2 : ℝ)).aemeasurable]
  have hp (r : ℝ) : (∫⁻ x : Space n, ‖𝓕⁻ (fun ξ : Space n => m (r, ξ)) x‖ₑ ^ (2 : ℝ)) =
      ∫⁻ ξ : Space n, ‖m (r, ξ)‖ₑ ^ (2 : ℝ) :=
    lintegral_fourierInv_cycles ((hmr r).integrable_of_hasCompactSupport (hmc r))
      ((hmr r).memLp_of_hasCompactSupport (hmc r))
  simp_rw [hp]
  rw [lintegral_lintegral_swap (hm.measurable.enorm.pow_const (2 : ℝ)).aemeasurable]
  apply lintegral_congr
  intro ξ
  simp only [m, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  exact lintegral_mul_const _ (((hA.comp (continuous_id.prodMk continuous_const)).measurable.enorm).pow_const (2 : ℝ))

theorem continuous_convolve_smoothRadiusKernel {n : ℕ} (A : ℝ × Space n → ℂ)
    (hA : Continuous A) (hc : HasCompactSupport A) {f : Space n → ℂ}
    (hf : Integrable f) : Continuous (convolveKernel (smoothRadiusKernel A hA) f) := by
  apply continuous_convolveKernel hf (differentiable_smoothRadiusKernel A hA hc).continuous
  refine ⟨∫ ξ, ‖smoothRadiusSymbol A hA ξ‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact norm_radiusFourierKernel_le_integral _ x

end OAI.Analysis.Fourier.SquareFunction
