import OAI.Analysis.Fourier.BochnerRiesz.FourierLimit

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem fourierInv_add_integrable {n : ℕ} {a b : Space n → ℂ}
    (ha : Integrable a) (hb : Integrable b) :
    𝓕⁻ (fun ξ ↦ a ξ + b ξ) = fun x ↦ 𝓕⁻ a x + 𝓕⁻ b x := by
  funext x
  simp only [OAI.Analysis.Fourier.SquareFunction.fourierInv_eq_spatialPhase_smul, smul_add]
  exact integral_add (OAI.Analysis.Fourier.SquareFunction.integrable_spatialPhase_smul x ha) (OAI.Analysis.Fourier.SquareFunction.integrable_spatialPhase_smul x hb)

theorem fourierInv_finset_sum {n : ℕ} {I : Type*} (s : Finset I) (a : I → Space n → ℂ)
    (ha : ∀ i ∈ s, Integrable (a i)) :
    𝓕⁻ (fun ξ ↦ ∑ i ∈ s, a i ξ) = fun x ↦ ∑ i ∈ s, 𝓕⁻ (a i) x := by
  funext x
  simp only [OAI.Analysis.Fourier.SquareFunction.fourierInv_eq_spatialPhase_smul, Finset.smul_sum]
  exact integral_finsetSum s (fun i hi ↦ OAI.Analysis.Fourier.SquareFunction.integrable_spatialPhase_smul x (ha i hi))

theorem fourierInv_const_mul {n : ℕ} (c : ℂ) (a : Space n → ℂ) :
    𝓕⁻ (fun ξ ↦ c * a ξ) = fun x ↦ c * 𝓕⁻ a x := by
  funext x
  simp only [OAI.Analysis.Fourier.SquareFunction.fourierInv_eq_spatialPhase_smul, smul_eq_mul]
  simp_rw [mul_left_comm _ c]
  exact integral_const_mul c _

theorem integrable_mul_of_bounded_left {n : ℕ} {a b : Space n → ℂ}
    (ha : AEStronglyMeasurable a volume) {C : ℝ} (hC : 0 ≤ C)
    (hbnd : ∀ ξ, ‖a ξ‖ ≤ C) (hb : Integrable b) : Integrable (fun ξ ↦ a ξ * b ξ) := by
  apply (hb.norm.const_mul C).mono (ha.mul hb.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun ξ ↦ by
    simpa only [Pi.mul_apply, norm_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hC, abs_norm] using
      mul_le_mul_of_nonneg_right (hbnd ξ) (norm_nonneg (b ξ))

theorem eLpNorm_fourierInv_finite_sum_le {n : ℕ} {I : Type*} (s : Finset I)
    (a : Space n → ℂ) (b : I → Space n → ℂ) (ha : Integrable a)
    (hb : ∀ i ∈ s, Integrable (b i)) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (𝓕⁻ (fun ξ ↦ a ξ + ∑ i ∈ s, b i ξ)) p volume ≤
      eLpNorm (𝓕⁻ a) p volume + ∑ i ∈ s, eLpNorm (𝓕⁻ (b i)) p volume := by
  have hs : Integrable (fun ξ : Space n ↦ ∑ i ∈ s, b i ξ) (volume : Measure (Space n)) :=
    integrable_finsetSum s hb
  rw [fourierInv_add_integrable ha hs, fourierInv_finset_sum s b hb]
  have hsum := eLpNorm_sum_le (μ := (volume : Measure (Space n)))
    (f := fun i ↦ 𝓕⁻ (b i)) (s := s) hp
  have hadd := eLpNorm_add_le (μ := (volume : Measure (Space n)))
    (f := 𝓕⁻ a) (g := fun x ↦ ∑ i ∈ s, 𝓕⁻ (b i) x) hp
  apply hadd.trans
  apply add_le_add le_rfl
  have he : (∑ i ∈ s, 𝓕⁻ (b i)) = fun x ↦ ∑ i ∈ s, 𝓕⁻ (b i) x := by
    funext x
    simp only [Finset.sum_apply]
  rw [he] at hsum
  exact hsum

end OAI.Analysis.Fourier.BochnerRiesz
