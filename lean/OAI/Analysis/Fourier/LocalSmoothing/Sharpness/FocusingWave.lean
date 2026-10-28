import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.AnnularPacket
import OAI.Analysis.Fourier.BochnerRiesz.Dilation
import OAI.Analysis.Fourier.LocalSmoothing.L2

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff

def focusingWave (n : ℕ) (N t : ℝ) (x : Space n) : ℂ :=
  OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ => phase (-t*‖ξ‖) * radialSymbol n (N⁻¹ • ξ)) x

theorem focusing_packet_wave {n : ℕ} {N t₀ : ℝ}
    {f : SchwartzMap (Space n) ℂ}
    (hf : ∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ = focusingSymbol n N t₀ ξ) (t : ℝ) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral (t₀+t) f x = focusingWave n N t x := by
  unfold OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral focusingWave
  congr 1
  funext ξ
  rw [hf]
  unfold focusingSymbol
  have he : Complex.exp (-Complex.I * (((t₀+t)*‖ξ‖:ℝ):ℂ)) = phase (-(t₀+t)*‖ξ‖) := by
    unfold phase
    congr 1
    push_cast
    ring
  rw [he,← mul_assoc,phase_mul]
  congr 2
  ring

theorem focusingWave_scale {n : ℕ} {N : ℝ} (hN : 0 < N) (t : ℝ) (x : Space n) :
    focusingWave n N t x = N^n • focusingWave n 1 (N*t) (N • x) := by
  let g : Space n → ℂ := fun ξ => phase (-(N*t)*‖ξ‖)*radialSymbol n ξ
  have hphase (ξ : Space n) : -(N*t)*‖N⁻¹ • ξ‖ = -t*‖ξ‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hN)]
    field_simp
  have he : (fun ξ : Space n => phase (-t*‖ξ‖)*radialSymbol n (N⁻¹ • ξ)) =
      (fun ξ => g (N⁻¹ • ξ)) := by
    funext ξ
    dsimp only [g]
    rw [hphase]
  unfold focusingWave
  rw [he,OAI.Analysis.Fourier.BochnerRiesz.angularInverse_dilate g (inv_pos.mpr hN)]
  simp only [inv_pow,inv_inv,inv_one,one_smul,g]

theorem focusing_packet_initial {n : ℕ} {N t₀ : ℝ}
    {f : SchwartzMap (Space n) ℂ}
    (hf : (f : Space n → ℂ) = OAI.Analysis.Fourier.LocalSmoothing.angularInverse (focusingSymbol n N t₀)) (x : Space n) :
    f x = focusingWave n N (-t₀) x := by
  rw [hf]
  simp only [focusingWave,neg_neg]
  rfl

theorem continuous_focusingWave (n : ℕ) {N : ℝ} (hN : N ≠ 0) :
    Continuous (fun z : Space n × ℝ => focusingWave n N z.2 z.1) := by
  obtain ⟨f,_,hf⟩ := exists_focusing_packet n hN 0
  have he : (fun z : Space n × ℝ => focusingWave n N z.2 z.1) =
      (fun z => OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1) := by
    funext z
    simpa only [zero_add] using (focusing_packet_wave hf z.2 z.1).symm
  rw [he]
  exact OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral f

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
