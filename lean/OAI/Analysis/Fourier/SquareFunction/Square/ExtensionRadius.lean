import OAI.Analysis.Fourier.SquareFunction.LocalSmoothing
import OAI.Analysis.Fourier.BochnerRiesz.LpExtension

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory FourierTransform Set
open scoped ENNReal
namespace OAI.Analysis.Fourier.SquareFunction

/-- The radius measure in Stein's square function. -/
def squareRadiusMeasure : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun r => (ENNReal.ofReal r)⁻¹)

theorem steinSquareFunction_eq_radius_eLpNorm {n : ℕ} (α : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f x =
      eLpNorm (fun r => radiusDerivativeCycles α r f x) 2 squareRadiusMeasure := by
  have hm := measurable_first_section (measurable_radiusDerivativeCycles α f) x
  rw [steinSquareFunction_eq_cycles,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hm.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat]
  rw [squareRadiusMeasure,lintegral_withDensity_eq_lintegral_mul₀]
  · congr 1
    apply lintegral_congr
    intro r
    simp only [Pi.mul_apply,ENNReal.rpow_two,div_eq_mul_inv,mul_comm]
  · exact (ENNReal.measurable_ofReal.inv).aemeasurable
  · exact (hm.enorm.pow_const (2 : ℝ)).aemeasurable

theorem ae_integrable_schwartz_radius_symbol {n : ℕ} [NeZero n] {α : ℝ}
    (hα : 1 / 2 < α) (f : SchwartzMap (Space n) ℂ) :
    ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
      Integrable (fun ξ => (radiusMultiplier α ‖ξ‖ r : ℂ) * (𝓕 f) ξ) := by
  have hF : (Lp.fourierTransformₗᵢ (Space n) ℂ) (f.toLp 2 volume) = (𝓕 f).toLp 2 volume :=
    SchwartzMap.toLp_fourier_eq f
  filter_upwards [ae_memLp_radius_symbol hα (f.toLp 2 volume)] with r hr
  have hi := integrable_radius_symbol α r _ hr
  rw [hF] at hi
  apply hi.congr
  filter_upwards [(𝓕 f).coeFn_toLp 2 volume] with ξ hξ
  rw [hξ]

theorem ae_radiusDerivativeCycles_sub {n : ℕ} [NeZero n] {α : ℝ}
    (hα : 1 / 2 < α) (f g : SchwartzMap (Space n) ℂ) (x : Space n) :
    (fun r => radiusDerivativeCycles α r (f-g) x) =ᵐ[squareRadiusMeasure]
      (fun r => radiusDerivativeCycles α r f x - radiusDerivativeCycles α r g x) := by
  apply (ae_withDensity_iff ENNReal.measurable_ofReal.inv).2
  filter_upwards [ae_integrable_schwartz_radius_symbol hα f,
    ae_integrable_schwartz_radius_symbol hα g] with r hf hg _
  unfold radiusDerivativeCycles
  rw [show 𝓕 (f-g) = 𝓕 f - 𝓕 g from
    map_sub (fourierCLM ℂ (SchwartzMap (Space n) ℂ)) f g]
  simp only [sub_apply,mul_sub]
  have hadd := OAI.Analysis.Fourier.BochnerRiesz.fourierInv_add_integrable hf hg.neg
  have hneg := OAI.Analysis.Fourier.BochnerRiesz.fourierInv_const_mul (-1 : ℂ)
    (fun ξ => (radiusMultiplier α ‖ξ‖ r : ℂ) * (𝓕 g) ξ)
  have hn : 𝓕⁻ (-(fun ξ => (radiusMultiplier α ‖ξ‖ r : ℂ) * (𝓕 g) ξ)) =
      - 𝓕⁻ (fun ξ => (radiusMultiplier α ‖ξ‖ r : ℂ) * (𝓕 g) ξ) := by
    simpa only [neg_one_mul,Pi.neg_apply] using! hneg
  have hh := congrFun hadd x
  rw [hn] at hh
  simpa only [Pi.neg_apply,sub_eq_add_neg] using hh

end OAI.Analysis.Fourier.SquareFunction
