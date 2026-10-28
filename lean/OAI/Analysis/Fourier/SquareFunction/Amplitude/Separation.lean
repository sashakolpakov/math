import OAI.Analysis.Fourier.SquareFunction.Amplitude.Kernel
import OAI.Analysis.Fourier.SquareFunction.Amplitude.Input
import OAI.Analysis.Fourier.SquareFunction.Radius.Amplitude

open OAI.Analysis.Fourier.Wave

/-! Exact amplitude separation in the continuous radius space. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform
open scoped ENNReal ContDiff

noncomputable def pureShellSymbol {n : ℕ} (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (ξ : Space n) : C(RadiusInterval, ℂ) :=
  radiusCurry (fun z : Space n × ℝ => φ ((z.2 - ‖z.1‖) / δ))
    (by have hφ := φ.continuous; fun_prop) ξ

theorem continuous_pureShellSymbol {n : ℕ} (φ : SchwartzMap ℝ ℂ) (δ : ℝ) :
    Continuous (pureShellSymbol (n := n) φ δ) := by
  unfold pureShellSymbol
  exact continuous_radiusCurry _ _

theorem norm_pureShellSymbol_le {n : ℕ} (φ : SchwartzMap ℝ ℂ) (δ : ℝ) (ξ : Space n) :
    ‖pureShellSymbol φ δ ξ‖ ≤ SchwartzMap.seminorm ℝ 0 0 φ := by
  apply (ContinuousMap.norm_le _ (apply_nonneg _ _)).2
  intro r
  exact SchwartzMap.norm_le_seminorm ℝ φ _

noncomputable def separatedAmplitudeSymbol {n : ℕ} (A : ℝ × Space n → ℂ)
    (φ : SchwartzMap ℝ ℂ) (δ η : ℝ) (ξ : Space n) : C(RadiusInterval, ℂ) :=
  OAI.Analysis.Fourier.WavePackets.partialRadiusFourier A η ξ • (radiusModulation η * pureShellSymbol φ δ ξ)

theorem continuous_separatedAmplitudeSymbol {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ) :
    Continuous (fun z : ℝ × Space n => separatedAmplitudeSymbol A φ δ z.1 z.2) :=
  (OAI.Analysis.Fourier.WavePackets.continuous_joint_partialRadiusFourier hA.continuous hc).smul
    ((continuous_radiusModulation.comp continuous_fst).mul
      ((continuous_pureShellSymbol φ δ).comp continuous_snd))

theorem norm_separatedAmplitudeSymbol_le {n : ℕ} (A : ℝ × Space n → ℂ)
    (φ : SchwartzMap ℝ ℂ) (δ η : ℝ) (ξ : Space n) :
    ‖separatedAmplitudeSymbol A φ δ η ξ‖ ≤
      ‖OAI.Analysis.Fourier.WavePackets.partialRadiusFourier A η ξ‖ * SchwartzMap.seminorm ℝ 0 0 φ := by
  rw [separatedAmplitudeSymbol, norm_smul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ‖radiusModulation η‖ * ‖pureShellSymbol φ δ ξ‖ := norm_mul_le _ _
    _ ≤ 1 * SchwartzMap.seminorm ℝ 0 0 φ :=
      mul_le_mul (norm_radiusModulation_le η) (norm_pureShellSymbol_le φ δ ξ)
        (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem integrable_separation_weight :
    Integrable (fun η : ℝ => (1 + |η|) ^ (-2 : ℝ)) := by
  have h : Integrable (fun η : ℝ => (1 + ‖η‖) ^ (-2 : ℝ)) :=
    integrable_one_add_norm (by norm_num)
  simpa only [Real.norm_eq_abs] using h

theorem continuous_left_slice {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {F : X × Y → Z}
    (hF : Continuous F) (y : Y) : Continuous (fun x => F (x, y)) :=
  hF.comp (continuous_id.prodMk continuous_const)

theorem integrable_of_separation_decay {H : Type*} [NormedAddCommGroup H]
    {F : ℝ → H} (hF : Continuous F) {C : ℝ}
    (hb : ∀ η, ‖F η‖ ≤ C * (1 + |η|) ^ (-2 : ℝ)) : Integrable F :=
  (integrable_separation_weight.const_mul C).mono' hF.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)

theorem integrable_separatedAmplitudeSymbol {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (ξ : Space n) : Integrable (fun η => separatedAmplitudeSymbol A φ δ η ξ) := by
  obtain ⟨C, hC, hb⟩ := amplitudeInput_bound hA hc
  have hm : Continuous (fun η => separatedAmplitudeSymbol A φ δ η ξ) :=
    continuous_left_slice (continuous_separatedAmplitudeSymbol hA hc φ δ) ξ
  apply integrable_of_separation_decay hm (C := C * SchwartzMap.seminorm ℝ 0 0 φ)
  intro η
  calc
    _ ≤ (C * (1 + |η|) ^ (-2 : ℝ)) * SchwartzMap.seminorm ℝ 0 0 φ :=
      (norm_separatedAmplitudeSymbol_le A φ δ η ξ).trans
        (mul_le_mul_of_nonneg_right ((hb η).1 ξ) (apply_nonneg _ _))
    _ = _ := by ring

theorem integral_separatedAmplitudeSymbol {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (ξ : Space n) :
    (∫ η : ℝ, separatedAmplitudeSymbol A φ δ η ξ) =
      amplitudeShellSymbol A hA.continuous φ δ ξ := by
  ext r
  rw [ContinuousMap.integral_apply (integrable_separatedAmplitudeSymbol hA hc φ δ ξ)]
  change (∫ η : ℝ, OAI.Analysis.Fourier.WavePackets.partialRadiusFourier A η ξ *
    (Complex.exp ((2 * Real.pi * (r : ℝ) * η : ℝ) * Complex.I) *
      φ (((r : ℝ) - ‖ξ‖) / δ))) = A (r, ξ) * φ (((r : ℝ) - ‖ξ‖) / δ)
  simp_rw [mul_left_comm (OAI.Analysis.Fourier.WavePackets.partialRadiusFourier A _ ξ), ← mul_assoc]
  rw [integral_mul_const, ← OAI.Analysis.Fourier.WavePackets.partialRadiusFourier_reconstruction hA hc]

end OAI.Analysis.Fourier.SquareFunction
