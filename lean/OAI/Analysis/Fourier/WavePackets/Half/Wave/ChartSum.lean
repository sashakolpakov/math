import OAI.Analysis.Fourier.WavePackets.Half.Wave.CapKernel
import OAI.Analysis.Fourier.BochnerRiesz.FiniteFourier

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter _root_.MeasureTheory
open scoped ContDiff Topology FourierTransform ENNReal

theorem fourierInv_sum_eLpNorm_le {n : ℕ} {I : Type*} [Fintype I]
    (f : I → Space n → ℂ) (hf : ∀ i, Integrable (f i)) :
    eLpNorm (𝓕⁻ (fun ξ => ∑ i, f i ξ)) 1 volume ≤
      ∑ i, eLpNorm (𝓕⁻ (f i)) 1 volume := by
  classical
  have he := OAI.Analysis.Fourier.BochnerRiesz.fourierInv_finset_sum Finset.univ f (fun i _ => hf i)
  rw [he]
  simpa only [Finset.sum_apply, Finset.sum_fn] using
    (eLpNorm_sum_le (p := (1 : ℝ≥0∞)) (μ := volume) (f := fun i => 𝓕⁻ (f i))
      (s := Finset.univ) le_rfl)

theorem waveAmplitude_integrable {n : ℕ} {b : Space n → ℂ}
    (hb : Continuous b) (hc : HasCompactSupport b) (h T : ℝ) :
    Integrable (waveAmplitude b h T) := by
  apply Continuous.integrable_of_hasCompactSupport _ (hasCompactSupport_waveAmplitude hc h T)
  unfold waveAmplitude
  fun_prop

/-- Summing the projective grid costs exactly the number of caps, whose
growth has the sphere dimension d rather than the ambient dimension d+1. -/
theorem uniform_wave_positive_chart_kernel {d : ℕ} {b : Space (d+1) → ℂ}
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) {a : ℝ} (ha : 0 < a)
    (hs : ∀ ξ ∈ tsupport b, a ≤ ξ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ γ : ℝ, 0 < γ → γ ≤ 1 → ∀ T ∈ Icc (1 : ℝ) 2,
      eLpNorm (𝓕⁻ (waveAmplitude b (γ^2) T)) 1 volume ≤ ENNReal.ofReal (C*(γ⁻¹)^d) := by
  classical
  obtain ⟨R,C₀,hR,hC₀,hpart⟩ := angular_chart_partition hb hc ha hs
  obtain ⟨C,hC,hkernel⟩ := uniform_wave_angularChart_kernel hb hc ha hs (R+1)
  refine ⟨(2*R+3)^d*C,mul_nonneg (pow_nonneg (by linarith) d) hC,?_⟩
  intro γ hγ hγ1 T hT
  let I := Fin d → Fin (2*angularGridSize R γ+1)
  let f : I → Space (d+1) → ℂ := fun k =>
    waveAmplitude (angularChartSymbol b γ (angularGridCenter R γ k)) (γ^2) T
  have hd := hpart γ hγ hγ1
  have hfi : ∀ k, Integrable (f k) := fun k =>
    waveAmplitude_integrable (hd.2.2 k).1.continuous (hd.2.2 k).2.1 (γ^2) T
  have he : waveAmplitude b (γ^2) T = fun ξ => ∑ k, f k ξ := by
    funext ξ
    simp only [f,waveAmplitude,← Finset.mul_sum]
    rw [congrFun hd.2.1 ξ]
  rw [he]
  calc
    _ ≤ ∑ k : I, eLpNorm (𝓕⁻ (f k)) 1 volume := fourierInv_sum_eLpNorm_le f hfi
    _ ≤ ∑ _k : I, ENNReal.ofReal C := Finset.sum_le_sum (fun k _ =>
      hkernel γ hγ hγ1 _ (angularGridCenter_bound hR hγ hγ1 k) T hT)
    _ = ENNReal.ofReal ((Fintype.card I : ℝ)*C) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      simp
    _ ≤ ENNReal.ofReal (((2*R+3)/γ)^d*C) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hd.1 hC)
    _ = ENNReal.ofReal (((2*R+3)^d*C)*(γ⁻¹)^d) := by
      congr 1
      rw [div_eq_mul_inv,mul_pow]
      ring

end OAI.Analysis.Fourier.WavePackets
