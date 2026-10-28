import OAI.Analysis.Fourier.BochnerRiesz.AnnularLittlewoodPaley

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem eLpNorm_rpow_eq_lintegral {X E : Type*} [MeasurableSpace X]
    [TopologicalSpace E] [ContinuousENorm E] {μ : Measure X} {f : X → E}
    {p : ℝ} (hp : 0 < p) (hf : AEStronglyMeasurable f μ) :
    eLpNorm f (ENNReal.ofReal p) μ ^ p = ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul]
  have h : (1 / p) * p = 1 := by field_simp
  rw [h, ENNReal.rpow_one]

theorem sum_rpow_le_vectorNorm_rpow {I : Type*} [Fintype I] (v : I → ℂ)
    {p : ℝ} (hp : 2 ≤ p) :
    ∑ i, ‖v i‖ₑ ^ p ≤ ‖OAI.Analysis.Fourier.SquareFunction.vectorNorm v‖ₑ ^ p := by
  have h := OAI.Analysis.Fourier.SquareFunction.sum_rpow_le_rpow_sum Finset.univ (fun i ↦ ‖v i‖ₑ ^ (2 : ℝ))
    (by linarith : 1 ≤ p / 2)
  rw [← OAI.Analysis.Fourier.SquareFunction.enorm_vectorNorm_sq, ← ENNReal.rpow_mul] at h
  rw [Real.enorm_eq_ofReal (OAI.Analysis.Fourier.SquareFunction.vectorNorm_nonneg v)]
  simpa only [← ENNReal.rpow_mul, show (2 : ℝ) * (p / 2) = p by ring] using h

theorem sum_eLpNorm_rpow_le_vectorNorm {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) (Q : I → X → ℂ) (hQ : ∀ i, Measurable (Q i))
    (s : Finset I) {p : ℝ} (hp : 2 ≤ p) :
    ∑ i ∈ s, eLpNorm (Q i) (ENNReal.ofReal p) μ ^ p ≤
      eLpNorm (fun x ↦ OAI.Analysis.Fourier.SquareFunction.vectorNorm (fun i : s ↦ Q i.val x)) (ENNReal.ofReal p) μ ^ p := by
  have hp0 : 0 < p := by linarith
  have hv : Measurable (fun x ↦ OAI.Analysis.Fourier.SquareFunction.vectorNorm (fun i : s ↦ Q i.val x)) :=
    OAI.Analysis.Fourier.SquareFunction.measurable_vectorNorm _ (fun i ↦ hQ i.val)
  have he (i : I) := eLpNorm_rpow_eq_lintegral hp0 (hQ i).aestronglyMeasurable (μ := μ)
  simp_rw [he]
  rw [← lintegral_finsetSum s (fun i _ ↦ (hQ i).enorm.pow_const p),
    eLpNorm_rpow_eq_lintegral hp0 hv.aestronglyMeasurable]
  apply lintegral_mono
  intro x
  have h := sum_rpow_le_vectorNorm_rpow (fun i : s ↦ Q i.val x) hp
  rw [Finset.sum_coe_sort s (fun i ↦ ‖Q i x‖ₑ ^ p)] at h
  exact h

theorem tsum_eLpNorm_rpow_le_of_square_function {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) (Q : I → X → ℂ) (hQ : ∀ i, Measurable (Q i))
    {p : ℝ} (hp : 2 ≤ p) {A : ℝ≥0∞}
    (hbound : ∀ s : Finset I,
      eLpNorm (fun x ↦ OAI.Analysis.Fourier.SquareFunction.vectorNorm (fun i : s ↦ Q i.val x)) (ENNReal.ofReal p) μ ≤ A) :
    ∑' i, eLpNorm (Q i) (ENNReal.ofReal p) μ ^ p ≤ A ^ p := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  exact (sum_eLpNorm_rpow_le_vectorNorm μ Q hQ s hp).trans
    (ENNReal.rpow_le_rpow (hbound s) (by linarith))

theorem eLpNorm_iSup_rpow_le_tsum {X I : Type*} [MeasurableSpace X] [Countable I]
    (μ : Measure X) (T : I → X → ℝ≥0∞) (hT : ∀ i, Measurable (T i))
    {p : ℝ} (hp : 0 < p) :
    eLpNorm (fun x ↦ ⨆ i, T i x) (ENNReal.ofReal p) μ ^ p ≤
      ∑' i, eLpNorm (T i) (ENNReal.ofReal p) μ ^ p := by
  rw [eLpNorm_rpow_eq_lintegral hp (Measurable.iSup hT).aestronglyMeasurable]
  simp only [enorm_eq_self]
  calc
    _ ≤ ∫⁻ x, ∑' i, T i x ^ p ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      have he : (⨆ i, T i x) ^ p = ⨆ i, T i x ^ p :=
        (ENNReal.orderIsoRpow p hp).map_iSup (fun i ↦ T i x)
      rw [he]
      exact iSup_le (fun i ↦ ENNReal.le_tsum (f := fun j ↦ T j x ^ p) i)
    _ = ∑' i, ∫⁻ x, T i x ^ p ∂μ := lintegral_tsum (fun i ↦ ((hT i).pow_const p).aemeasurable)
    _ = _ := by
      apply tsum_congr
      intro i
      simpa only [enorm_eq_self] using (eLpNorm_rpow_eq_lintegral hp (hT i).aestronglyMeasurable (μ := μ)).symm

/-- Countably many local maximal estimates are summed using an actual
finite-family square-function bound. -/
theorem eLpNorm_iSup_le_from_square_function {X I : Type*} [MeasurableSpace X] [Countable I]
    (μ : Measure X) (T : I → X → ℝ≥0∞) (Q : I → X → ℂ)
    (hT : ∀ i, Measurable (T i)) (hQ : ∀ i, Measurable (Q i))
    {p : ℝ} (hp : 2 ≤ p) {A C : ℝ≥0∞}
    (hlocal : ∀ i, eLpNorm (T i) (ENNReal.ofReal p) μ ≤ C * eLpNorm (Q i) (ENNReal.ofReal p) μ)
    (hsquare : ∀ s : Finset I,
      eLpNorm (fun x ↦ OAI.Analysis.Fourier.SquareFunction.vectorNorm (fun i : s ↦ Q i.val x)) (ENNReal.ofReal p) μ ≤ A) :
    eLpNorm (fun x ↦ ⨆ i, T i x) (ENNReal.ofReal p) μ ≤ C * A := by
  have hp0 : 0 < p := by linarith
  have hs := tsum_eLpNorm_rpow_le_of_square_function μ Q hQ hp hsquare
  have H : eLpNorm (fun x ↦ ⨆ i, T i x) (ENNReal.ofReal p) μ ^ p ≤ (C * A) ^ p := by
    calc
      _ ≤ ∑' i, eLpNorm (T i) (ENNReal.ofReal p) μ ^ p := eLpNorm_iSup_rpow_le_tsum μ T hT hp0
      _ ≤ ∑' i, C ^ p * eLpNorm (Q i) (ENNReal.ofReal p) μ ^ p := by
        apply ENNReal.tsum_le_tsum
        intro i
        simpa only [ENNReal.mul_rpow_of_nonneg _ _ hp0.le] using ENNReal.rpow_le_rpow (hlocal i) hp0.le
      _ = C ^ p * ∑' i, eLpNorm (Q i) (ENNReal.ofReal p) μ ^ p := ENNReal.tsum_mul_left
      _ ≤ C ^ p * A ^ p := mul_le_mul' le_rfl hs
      _ = _ := (ENNReal.mul_rpow_of_nonneg _ _ hp0.le).symm
  have HH := ENNReal.rpow_le_rpow H (le_of_lt (one_div_pos.mpr hp0))
  simpa only [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one] using HH

end OAI.Analysis.Fourier.BochnerRiesz
