import OAI.Analysis.Fourier.WavePackets.Half.Wave.LowPartition

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter _root_.MeasureTheory
open scoped ContDiff Topology FourierTransform ENNReal

theorem continuous_lowWaveAnnulus {n : ℕ} {b χ : Space n → ℂ}
    (hb : Continuous b) (hχ : Continuous χ) (r T : ℝ) :
    Continuous (lowWaveAnnulus b χ r T) := by
  unfold lowWaveAnnulus
  fun_prop

theorem integrable_lowWaveAnnulus {n : ℕ} {b χ : Space n → ℂ}
    (hb : Continuous b) (hχ : Continuous χ) (hc : HasCompactSupport χ) (r T : ℝ) :
    Integrable (lowWaveAnnulus b χ r T) := by
  apply (continuous_lowWaveAnnulus hb hχ r T).integrable_of_hasCompactSupport
  exact (hc.mul_left).mul_right

theorem angularInverse_finset_sum {n : ℕ} {I : Type*} (s : Finset I)
    (f : I → Space n → ℂ) (hf : ∀ i ∈ s, Integrable (f i)) :
    OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ => ∑ i ∈ s,f i ξ) = fun x => ∑ i ∈ s, OAI.Analysis.Fourier.LocalSmoothing.angularInverse (f i) x := by
  funext x
  simp only [OAI.Analysis.Fourier.LocalSmoothing.angularInverse,Finset.mul_sum,integral_finsetSum s
    (fun i hi => OAI.Analysis.Fourier.LocalSmoothing.integrable_angularKernel_mul (hf i hi) x),Finset.smul_sum]

theorem integrable_lowRemainder {n : ℕ} {χ : Space n → ℂ}
    (hχ : Continuous χ) (hc : HasCompactSupport χ) (T : ℝ) :
    Integrable (lowRemainder χ T) := by
  apply Continuous.integrable_of_hasCompactSupport
  · unfold lowRemainder
    have := (OAI.Analysis.Fourier.LocalSmoothing.contDiff_smoothingLowCutoff n).continuous
    fun_prop
  · exact hc.mul_right.mul_right

theorem tendsto_angularInverse_low_sum {n : ℕ} {χ : Space n → ℂ}
    (hχ : Continuous χ) (hc : HasCompactSupport χ) (T : ℝ) (x : Space n) :
    Tendsto (fun N : ℕ => OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ => ∑ k ∈ Finset.range N,
      lowWaveAnnulus inwardAnnulus χ (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale k) T ξ) x)
      atTop (𝓝 (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (lowRemainder χ T) x)) := by
  unfold OAI.Analysis.Fourier.LocalSmoothing.angularInverse
  apply Tendsto.const_smul
  apply tendsto_integral_of_dominated_convergence (fun ξ => 4*‖χ ξ‖)
  · intro N
    apply (OAI.Analysis.Fourier.LocalSmoothing.integrable_angularKernel_mul _ x).aestronglyMeasurable
    exact integrable_finsetSum _ (fun k _ => integrable_lowWaveAnnulus
      (contDiff_inwardAnnulus n).continuous hχ hc _ T)
  · exact (hχ.integrable_of_hasCompactSupport hc).norm.const_mul 4
  · intro N
    filter_upwards [] with ξ
    simpa [norm_mul,Complex.norm_exp] using norm_lowWaveAnnulus_sum_le χ T N ξ
  · filter_upwards [] with ξ
    exact tendsto_const_nhds.mul (tendsto_lowWaveAnnulus_sum χ T ξ)

/-- The singularity at zero is removed by a geometrically summable
dyadic gain, not by assuming that the wave symbol is smooth there. -/
theorem uniform_lowRemainder_kernel {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T ∈ Icc (1:ℝ) 2,
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (lowRemainder χ T)) 1 volume ≤ ENNReal.ofReal C := by
  obtain ⟨C,hC,hbound⟩ := uniform_lowWaveAnnulus_kernel
    (contDiff_inwardAnnulus n) (hasCompactSupport_inwardAnnulus n)
    (zero_notMem_tsupport_inwardAnnulus n) hχ
  refine ⟨2*C,mul_nonneg (by norm_num) hC,?_⟩
  intro T hT
  let f : ℕ → Space n → ℂ := fun k => lowWaveAnnulus inwardAnnulus χ (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale k) T
  have hi (k : ℕ) : Integrable (f k) := integrable_lowWaveAnnulus
    (contDiff_inwardAnnulus n).continuous hχ.continuous hc _ T
  have hsum (N : ℕ) : (∑ k ∈ Finset.range N,OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale k) ≤ 2 := by
    have ht : (∑ k ∈ Finset.range N,OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale k) = 2*(1-OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale N) := by
      induction N with
      | zero => simp [OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale]
      | succ N ih => rw [Finset.sum_range_succ,ih,OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale_succ]; ring
    rw [ht]
    linarith [OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale_pos N]
  have hpartial (N : ℕ) :
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ => ∑ k ∈ Finset.range N,f k ξ)) 1 volume ≤
        ENNReal.ofReal (2*C) := by
    rw [angularInverse_finset_sum _ f (fun k _ => hi k)]
    calc
      _ ≤ ∑ k ∈ Finset.range N,eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (f k)) 1 volume := by
        simpa only [Finset.sum_fn] using
          (eLpNorm_sum_le (s := Finset.range N) (f := fun k => OAI.Analysis.Fourier.LocalSmoothing.angularInverse (f k)) le_rfl)
      _ ≤ ∑ k ∈ Finset.range N,ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale k*C) :=
        Finset.sum_le_sum (fun k _ => hbound _ (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale_pos k)
          (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale_le_one k) T hT)
      _ = ENNReal.ofReal ((∑ k ∈ Finset.range N,OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale k)*C) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ =>
          mul_nonneg (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale_pos k).le hC),Finset.sum_mul]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hsum N) hC)
  apply Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (Eventually.of_forall hpartial)
  · intro N
    exact (OAI.Analysis.Fourier.BochnerRiesz.continuous_angularInverse
      (integrable_finsetSum _ (fun k _ => hi k))).aestronglyMeasurable
  · exact (OAI.Analysis.Fourier.BochnerRiesz.continuous_angularInverse
      (integrable_lowRemainder hχ.continuous hc T)).aestronglyMeasurable
  · exact Eventually.of_forall (tendsto_angularInverse_low_sum hχ.continuous hc T)

end OAI.Analysis.Fourier.WavePackets
