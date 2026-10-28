import OAI.Analysis.Fourier.WavePackets.Half.Wave.ChartSum

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter _root_.MeasureTheory
open scoped ContDiff Topology FourierTransform ENNReal

/-- Sharp L¹ half-wave kernel growth on any smooth compact annulus.
The finite atlas and all shrinking-cap estimates are constructed. -/
theorem uniform_wave_annular_kernel_sqrt {d : ℕ} {φ : Space (d+1) → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hz : 0 ∉ tsupport φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ, 0 < γ → γ ≤ 1 → ∀ T ∈ Icc (1 : ℝ) 2,
      eLpNorm (𝓕⁻ (waveAmplitude φ (γ^2) T)) 1 volume ≤ ENNReal.ofReal (C*(γ⁻¹)^d) := by
  classical
  obtain ⟨s,b,a,hb,hsum⟩ := finite_angular_atlas hφ hc hz
  choose C hC hkernel using fun i : s =>
    uniform_wave_positive_chart_kernel (hb i).1 (hb i).2.1 (hb i).2.2.1 (hb i).2.2.2.1
  have hCsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ => hC i)
  refine ⟨1+∑ i,C i,by linarith,?_⟩
  intro γ hγ hγ1 T hT
  let f : s → Space (d+1) → ℂ := fun i ξ => waveAmplitude (b i) (γ^2) T (i.val ξ)
  have hfi (i : s) : Integrable (f i) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (contDiff_waveAmplitude (hb i).1 (by
        intro h
        have := (hb i).2.2.2.1 0 h
        simp only [PiLp.zero_apply] at this
        linarith [(hb i).2.2.1]) (γ^2) T).continuous.comp i.val.continuous
    · exact (hasCompactSupport_waveAmplitude (hb i).2.1 (γ^2) T).comp_homeomorph i.val.toHomeomorph
  have he : waveAmplitude φ (γ^2) T = fun ξ => ∑ i, f i ξ := by
    funext ξ
    simp only [f,waveAmplitude,LinearIsometryEquiv.norm_map,← Finset.mul_sum]
    rw [congrFun hsum ξ]
  have hbound (i : s) : eLpNorm (𝓕⁻ (f i)) 1 volume ≤ ENNReal.ofReal (C i*(γ⁻¹)^d) := by
    have hzi : (0 : Space (d+1)) ∉ tsupport (b i) := by
      intro h
      have := (hb i).2.2.2.1 0 h
      simp only [PiLp.zero_apply] at this
      linarith [(hb i).2.2.1]
    change eLpNorm (𝓕⁻ (waveAmplitude (b i) (γ^2) T ∘ i.val)) 1 volume ≤ _
    have hcomp := eLpNorm_fourierInv_comp_smooth
      (contDiff_waveAmplitude (hb i).1 hzi (γ^2) T)
      (hasCompactSupport_waveAmplitude (hb i).2.1 (γ^2) T) i.val.toContinuousLinearEquiv
    simpa only using! hcomp.trans_le (hkernel i γ hγ hγ1 T hT)
  rw [he]
  calc
    _ ≤ ∑ i, eLpNorm (𝓕⁻ (f i)) 1 volume := fourierInv_sum_eLpNorm_le f hfi
    _ ≤ ∑ i, ENNReal.ofReal (C i*(γ⁻¹)^d) := Finset.sum_le_sum (fun i _ => hbound i)
    _ = ENNReal.ofReal ((∑ i,C i)*(γ⁻¹)^d) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hC i) (by positivity)),
        Finset.sum_mul]
    _ ≤ ENNReal.ofReal ((1+∑ i,C i)*(γ⁻¹)^d) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

theorem inv_sqrt_pow_eq_rpow {h : ℝ} (hh : 0 < h) (d : ℕ) :
    ((Real.sqrt h)⁻¹)^d = h^(-(d : ℝ)/2) := by
  rw [← Real.rpow_natCast,Real.inv_rpow (Real.sqrt_nonneg h),Real.sqrt_eq_rpow,
    ← Real.rpow_mul hh.le,← Real.rpow_neg hh.le]
  congr 1
  ring

theorem uniform_wave_annular_kernel {d : ℕ} {φ : Space (d+1) → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hz : 0 ∉ tsupport φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ T ∈ Icc (1 : ℝ) 2,
      eLpNorm (𝓕⁻ (waveAmplitude φ h T)) 1 volume ≤ ENNReal.ofReal (C*h^(-(d : ℝ)/2)) := by
  obtain ⟨C,hC,hkernel⟩ := uniform_wave_annular_kernel_sqrt hφ hc hz
  refine ⟨C,hC,?_⟩
  intro h hh hh1 T hT
  have hsq1 : Real.sqrt h ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hh1
  have H := hkernel (Real.sqrt h) (Real.sqrt_pos.2 hh) hsq1 T hT
  simpa only [Real.sq_sqrt hh.le,inv_sqrt_pow_eq_rpow hh d] using H

end OAI.Analysis.Fourier.WavePackets
