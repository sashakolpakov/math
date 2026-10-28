import OAI.Analysis.Fourier.BochnerRiesz.KernelDilation

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter Metric FourierTransform
open scoped ENNReal Topology
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz


theorem bochnerRiesz_compact_tail {n : ℕ} (hn : 1 ≤ n) {δ : ℝ}
    (hδ : ((n : ℝ) - 1) / 2 < δ) (f : SchwartzMap (Space n) ℂ)
    {S : ℝ} (hS : 0 ≤ S) (hs : ∀ y, S < ‖y‖ → f y = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ x : Space n, 2 * S + 2 < ‖x‖ →
      ‖OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x‖ ≤ C * (1 + ‖x‖) ^ (-(((n : ℝ) + 2 * δ + 1) / 2)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < δ := by linarith
  obtain ⟨C, hC, hb⟩ := brDilatedKernel_compact_tail hn hδ
  refine ⟨C * (∫ y, ‖f y‖), mul_nonneg hC.le (integral_nonneg (fun _ => norm_nonneg _)), ?_⟩
  intro R hR x hx
  let L := C * (1 + ‖x‖) ^ (-(((n : ℝ) + 2 * δ + 1) / 2))
  have hK := continuous_brDilatedKernel (n := n) hd R
  have hKb := bddAbove_norm_brDilatedKernel hn hd R
  have hi := OAI.Analysis.Fourier.SquareFunction.integrable_convolveKernel_integrand f.integrable hK hKb x
  rw [bochnerRiesz_eq_convolve_brDilatedKernel hd (zero_lt_one.trans_le hR) f.integrable,
    OAI.Analysis.Fourier.SquareFunction.convolveKernel]
  calc
    _ ≤ ∫ y, ‖f y • brDilatedKernel δ R (x - y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ‖f y‖ * L := by
      apply integral_mono hi.norm (f.integrable.norm.mul_const L)
      intro y
      dsimp only
      by_cases hy : ‖y‖ ≤ S
      · rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hb R hR S hS x y hx hy) (norm_nonneg _)
      · simp only [hs y (lt_of_not_ge hy), zero_smul, norm_zero, zero_mul, le_refl]
    _ = _ := by rw [integral_mul_const]; dsimp [L]; ring

theorem exists_integrable_bochnerRiesz_majorant_compact {n : ℕ} (hn : 1 ≤ n) {δ : ℝ}
    (hδ : ((n : ℝ) - 1) / 2 < δ) (f : SchwartzMap (Space n) ℂ)
    {S : ℝ} (hS : 0 ≤ S) (hs : ∀ y, S < ‖y‖ → f y = 0) :
    ∃ G : Space n → ℝ, Integrable G ∧ ∀ R : ℝ, 1 ≤ R → ∀ x, ‖OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x‖ ≤ G x := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < δ := by linarith
  obtain ⟨C, hC, hb⟩ := bochnerRiesz_compact_tail hn hδ f hS hs
  let M := ∫ ξ, ‖(𝓕 f : SchwartzMap (Space n) ℂ) ξ‖
  let B := closedBall (0 : Space n) (2 * S + 2)
  let w := fun x : Space n => (1 + ‖x‖) ^ (-(((n : ℝ) + 2 * δ + 1) / 2))
  have hw (x) : 0 ≤ w x := Real.rpow_nonneg (by positivity) _
  have hwi : Integrable w := by
    apply integrable_one_add_norm
    simp only [Space, finrank_euclideanSpace, Fintype.card_fin]
    linarith
  have hBc : IntegrableOn (fun _ : Space n => M) B volume :=
    integrableOn_const (show volume B ≠ ⊤ from measure_closedBall_lt_top.ne)
  have hBi : Integrable (B.indicator (fun _ : Space n => M)) :=
    (integrable_indicator_iff measurableSet_closedBall).mpr hBc
  refine ⟨fun x => B.indicator (fun _ => M) x + C * w x, hBi.add (hwi.const_mul C), ?_⟩
  intro R hR x
  dsimp only
  by_cases hx : x ∈ B
  · rw [indicator_of_mem hx]
    exact (norm_bochnerRiesz_le_fourier_mass hd.le f R x).trans (le_add_of_nonneg_right (mul_nonneg hC (hw x)))
  · rw [indicator_of_notMem hx, zero_add]
    apply hb R hR x
    simpa only [B, mem_closedBall, dist_zero_right, not_le] using hx

/-- At the integrable-kernel endpoint, compactly supported smooth data have
an integrable majorant independent of every radius `R ≥ 1`. -/
theorem tendsto_bochnerRiesz_L1_compact {n : ℕ} (hn : 1 ≤ n) {δ : ℝ}
    (hδ : ((n : ℝ) - 1) / 2 < δ) (f : SchwartzMap (Space n) ℂ)
    {S : ℝ} (hS : 0 ≤ S) (hs : ∀ y, S < ‖y‖ → f y = 0) :
    Tendsto (fun R : ℝ => eLpNorm (fun x => OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x - f x) 1 volume) atTop (𝓝 0) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < δ := by linarith
  obtain ⟨G, hGi, hG⟩ := exists_integrable_bochnerRiesz_majorant_compact hn hδ f hS hs
  have ht : Tendsto (fun R : ℝ => ∫ x, ‖OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x - f x‖) atTop
      (𝓝 (∫ _ : Space n, (0 : ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => G x + ‖f x‖)
    · exact Eventually.of_forall fun R =>
        (((continuous_bochnerRiesz_schwartz hd.le R f).sub f.continuous).norm).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
      apply Eventually.of_forall
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact (norm_sub_le _ _).trans (add_le_add (hG R hR x) le_rfl)
    · exact hGi.add f.integrable.norm
    · apply Eventually.of_forall
      intro x
      simpa only [sub_self, norm_zero] using
        ((OAI.Analysis.Fourier.SquareFunction.tendsto_bochnerRiesz_schwartz hd.le f x).sub (tendsto_const_nhds (x := f x))).norm
  have ht' : Tendsto (fun R : ℝ => ENNReal.ofReal (∫ x, ‖OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x - f x‖)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, integral_zero, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  apply ht'.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  have hi : Integrable (fun x => OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x - f x) :=
    (hGi.add f.integrable.norm).mono'
      ((continuous_bochnerRiesz_schwartz hd.le R f).sub f.continuous).aestronglyMeasurable
      (Eventually.of_forall fun x => (norm_sub_le _ _).trans (add_le_add (hG R hR x) le_rfl))
  rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
    ofReal_integral_norm_eq_lintegral_enorm hi]

end OAI.Analysis.Fourier.BochnerRiesz
