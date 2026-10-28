import OAI.Analysis.Fourier.WavePackets.Half.Wave.LowKernel

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology
noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

theorem uniform_lowWaveAnnulus_kernel_compact {n : ℕ} {b χ : Space n → ℂ}
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) (hz : 0 ∉ tsupport b)
    (hχ : ContDiff ℝ ∞ χ) {K : Set ℝ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ T ∈ K,
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (lowWaveAnnulus b χ r T)) 1 volume ≤ ENNReal.ofReal (r*C) := by
  obtain ⟨C,hC,hbound⟩ := OAI.Analysis.Fourier.BochnerRiesz.uniform_angularInverse_L1
    (hK.prod (isCompact_Icc (a := (0:ℝ)) (b := 1))) hc
    (contDiff_lowWaveFamily hb hχ hz) (lowWaveFamily_support b χ)
  refine ⟨C,hC,?_⟩
  intro r hr hr1 T hT
  have hi : Integrable (fun ξ => lowWaveFamily b χ ((T,r),ξ)) := by
    apply ((contDiff_lowWaveFamily hb hχ hz).continuous.comp
      (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    apply hc.of_isClosed_subset (isClosed_tsupport _)
    intro ξ hξ
    exact ((lowWaveFamily_support b χ) (tsupport_comp_subset_preimage _
      (continuous_const.prodMk continuous_id) hξ)).2
  have he : OAI.Analysis.Fourier.LocalSmoothing.angularInverse (lowWaveAnnulus b χ r T) = fun x =>
      r • OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ => lowWaveFamily b χ ((T,r),r⁻¹ • ξ)) x := by
    rw [lowWaveAnnulus_eq_dilate b χ hr T]
    exact funext (OAI.Analysis.Fourier.BochnerRiesz.angularInverse_smul_real r _)
  rw [he]
  change eLpNorm (r • (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ => lowWaveFamily b χ ((T,r),r⁻¹ • ξ))))
    1 volume ≤ _
  rw [eLpNorm_const_smul,Real.enorm_eq_ofReal hr.le,
    OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_angularInverse_dilate_one hi (inv_pos.mpr hr),
    ENNReal.ofReal_mul hr.le]
  exact mul_le_mul' le_rfl (hbound (T,r) ⟨hT,hr.le,hr1⟩).2

theorem uniform_lowRemainder_kernel_compact {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) {K : Set ℝ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T ∈ K,
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (lowRemainder χ T)) 1 volume ≤ ENNReal.ofReal C := by
  obtain ⟨C,hC,hbound⟩ := uniform_lowWaveAnnulus_kernel_compact
    (contDiff_inwardAnnulus n) (hasCompactSupport_inwardAnnulus n)
    (zero_notMem_tsupport_inwardAnnulus n) hχ hK
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

theorem contDiff_fixed_waveAmplitude {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hz : 0 ∉ tsupport χ) :
    ContDiff ℝ ∞ (fun z : ℝ × Space n ↦ waveAmplitude χ 1 z.1 z.2) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hx : z.2 = 0
  · have he := (notMem_tsupport_iff_eventuallyEq.mp (hx ▸ hz)).comp_tendsto
      (continuous_snd.tendsto z)
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    simp only [waveAmplitude, show χ y.2 = 0 from hy, mul_zero]
  · have hn : ContDiffAt ℝ ∞ (fun y : ℝ × Space n ↦ ‖y.2‖) z :=
      (contDiffAt_norm ℝ hx).comp z contDiffAt_snd
    change ContDiffAt ℝ ∞ (fun y : ℝ × Space n ↦
      Complex.exp (-Complex.I * (y.1 / 1 * ‖y.2‖ : ℝ)) * χ y.2) z
    simp only [div_one]
    exact (Complex.contDiff_exp.contDiffAt.comp z
        (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp z
          (contDiffAt_fst.mul hn)))).mul (hχ.contDiffAt.comp z contDiffAt_snd)

theorem tsupport_fixed_waveAmplitude {n : ℕ} (χ : Space n → ℂ) :
    tsupport (fun z : ℝ × Space n ↦ waveAmplitude χ 1 z.1 z.2) ⊆
      univ ×ˢ tsupport χ := by
  intro z hz
  refine ⟨trivial,?_⟩
  exact tsupport_comp_subset_preimage χ continuous_snd
    (tsupport_mul_subset_right (f := fun z : ℝ × Space n ↦
      Complex.exp (-Complex.I * (z.1 / 1 * ‖z.2‖ : ℝ))) hz)

/-- Every smooth compact cutoff has a uniformly integrable wave kernel
on an arbitrary compact time interval, including time zero. -/
theorem uniform_fixed_frequency_kernel_compact {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) {K : Set ℝ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ T ∈ K,
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (waveAmplitude χ 1 T)) 1 volume ≤ ENNReal.ofReal C := by
  obtain ⟨A,hA,ha⟩ := fixed_smooth_kernel_bound (lowCore_smooth hχ) (lowCore_compact hc)
  obtain ⟨B,hB,hb⟩ := uniform_lowRemainder_kernel_compact hχ hc hK
  obtain ⟨D,hD,hd⟩ := OAI.Analysis.Fourier.BochnerRiesz.uniform_angularInverse_L1 hK (highCore_compact hc)
    (contDiff_fixed_waveAmplitude (highCore_smooth hχ) (highCore_away χ))
    (tsupport_fixed_waveAmplitude (highCore χ))
  refine ⟨A+B+D+1,by positivity,?_⟩
  intro T hT
  have hai : Integrable (lowCore χ) volume :=
    (lowCore_smooth hχ).continuous.integrable_of_hasCompactSupport (lowCore_compact hc)
  have hdi := waveAmplitude_integrable (highCore_smooth hχ).continuous (highCore_compact hc) 1 T
  rw [waveAmplitude_low_decomposition]
  exact (inverse_kernel_triple_bound hai (integrable_lowRemainder hχ.continuous hc T)
    hdi hA hB hD ha (hb T hT) (hd T hT).2).trans
      (ENNReal.ofReal_le_ofReal (by linarith))

end OAI.Analysis.Fourier.WavePackets
