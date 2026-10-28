import OAI.Analysis.Fourier.SquareFunction.Summation
import OAI.Analysis.Fourier.SquareFunction.EnvelopeLp
import OAI.Analysis.Fourier.BochnerRiesz.Geometric

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.SquareFunction


theorem eLpNorm_dyadic_envelope_sum_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {T : ℕ → X → ℝ≥0∞} (hT : ∀ j, Measurable (T j))
    {p : ℝ} (hp : 1 ≤ p) {A δ σ : ℝ} (hA : 0 ≤ A) (hgap : σ < δ)
    (J : ℕ) (F : ℝ≥0∞)
    (hb : ∀ j, eLpNorm (T j) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (A * (((2 : ℝ) ^ (J + j)) ^ (-δ) * ((2 : ℝ) ^ (J + j)) ^ σ)) * F) :
    eLpNorm (fun x => ∑' j, T j x) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (A * (1 - (2 : ℝ) ^ (σ - δ))⁻¹) * F := by
  apply (ennreal_eLpNorm_tsum_le hT hp).trans
  apply (ENNReal.tsum_le_tsum hb).trans
  rw [ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro N
  calc
    _ = ENNReal.ofReal (A * (∑ j ∈ Finset.range N,
        ((2 : ℝ) ^ (J + j)) ^ (-δ) * ((2 : ℝ) ^ (J + j)) ^ σ)) * F := by
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity),
        ← Finset.mul_sum]
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (OAI.Analysis.Fourier.BochnerRiesz.sum_dyadic_rpow_product_le hgap J N) hA)) le_rfl

end OAI.Analysis.Fourier.SquareFunction
