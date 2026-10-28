import OAI.Analysis.Fourier.SquareFunction.Maximal.BRSmooth
import OAI.Analysis.Fourier.SquareFunction.Maximal.BRPartition

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.SquareFunction


theorem maximalShellCycles_ne_top {n : ℕ} (φ : SchwartzMap ℝ ℂ) (Λ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) : OAI.Analysis.Fourier.BochnerRiesz.maximalShellCycles φ Λ f x ≠ ⊤ := by
  let C : ℝ := SchwartzMap.seminorm ℝ 0 0 φ
  have hb : OAI.Analysis.Fourier.BochnerRiesz.maximalShellCycles φ Λ f x ≤ ENNReal.ofReal (C * ∫ ξ, ‖(𝓕 f : SchwartzMap (Space n) ℂ) ξ‖) := by
    apply iSup_le
    intro ρ
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    rw [OAI.Analysis.Fourier.BochnerRiesz.dilatedShellCycles, Real.fourierInv_eq_fourier_neg]
    apply (VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
      (innerₗ (Space n)) _ (-x)).trans
    rw [← integral_const_mul]
    apply integral_mono (OAI.Analysis.Fourier.BochnerRiesz.integrable_dilatedShellSymbol φ Λ ρ.val f).norm
      ((𝓕 f).integrable.norm.const_mul C)
    intro ξ
    dsimp only
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℝ φ _) (norm_nonneg _)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb

theorem brScaledPacket_maximal_bound {n : ℕ} {δ : ℝ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hzero : 0 ∉ tsupport χ) :
    ∃ K : ℝ, 0 < K ∧ ∀ j : ℕ, ∀ h : ℝ, 0 < h → ∀ f : SchwartzMap (Space n) ℂ, ∀ x,
      ‖brScaledPacket δ χ j h f x‖ₑ ≤ ENNReal.ofReal K *
        ballMaximal volume (OAI.Analysis.Fourier.BochnerRiesz.maximalShellCycles (OAI.Analysis.Fourier.BochnerRiesz.dyadicPowerProfile δ) ((2 : ℝ) ^ j) f) x := by
  obtain ⟨K, hK, hb⟩ := smooth_fourier_multiplier_maximal_envelope
    (OAI.Analysis.Fourier.BochnerRiesz.contDiff_brExteriorSymbol δ hχ hzero) (OAI.Analysis.Fourier.BochnerRiesz.hasCompactSupport_brExteriorSymbol δ hc)
  refine ⟨K, hK, ?_⟩
  intro j h hh f x
  apply hb h hh _ (OAI.Analysis.Fourier.BochnerRiesz.integrable_dilatedShellSymbol _ _ _ f) _
    (OAI.Analysis.Fourier.BochnerRiesz.measurable_maximalShellCycles _ _ f) _ x
  intro y
  change ‖OAI.Analysis.Fourier.BochnerRiesz.dilatedShellCycles (OAI.Analysis.Fourier.BochnerRiesz.dyadicPowerProfile δ) ((2 : ℝ) ^ j)
    (h * (2 * Real.pi) * (2 : ℝ) ^ j) f y‖ₑ ≤
    OAI.Analysis.Fourier.BochnerRiesz.maximalShellCycles (OAI.Analysis.Fourier.BochnerRiesz.dyadicPowerProfile δ) ((2 : ℝ) ^ j) f y
  exact le_iSup_of_le (⟨h * (2 * Real.pi) * (2 : ℝ) ^ j,
    show 0 < h * (2 * Real.pi) * (2 : ℝ) ^ j by positivity⟩ : Set.Ioi (0 : ℝ)) le_rfl

theorem brScaledInterior_maximal_bound {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {J : ℕ} (hJ : 2 ≤ J) :
    ∃ B : ℝ, 0 < B ∧ ∀ h : ℝ, 0 < h → ∀ f : SchwartzMap (Space n) ℂ, ∀ x,
      ‖brScaledInterior δ J h f x‖ₑ ≤
        ENNReal.ofReal B * ballMaximal volume (fun y => ‖f y‖ₑ) x := by
  obtain ⟨B, hB, hb⟩ := smooth_fourier_multiplier_maximal_envelope
    (OAI.Analysis.Fourier.BochnerRiesz.contDiff_brInteriorSymbol hδ hJ) (OAI.Analysis.Fourier.BochnerRiesz.hasCompactSupport_brInteriorSymbol hδ J)
  refine ⟨B, hB, ?_⟩
  intro h hh f x
  apply hb h hh _ (𝓕 f).integrable _ f.continuous.measurable.enorm _ x
  intro y
  simp only [← SchwartzMap.fourierInv_coe, fourierInv_fourier_eq, le_refl]

end OAI.Analysis.Fourier.SquareFunction
