import OAI.Analysis.Fourier.BochnerRiesz.Geometric
import OAI.Analysis.Fourier.BochnerRiesz.FiniteFourier

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem finite_dyadic_eLpNorm_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (a : X → ℂ) (T : ℕ → X → ℂ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {A B δ σ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hgap : σ < δ)
    (J N : ℕ) (F : ℝ≥0∞) (ha : eLpNorm a p μ ≤ ENNReal.ofReal B * F)
    (hT : ∀ j, eLpNorm (T j) p μ ≤
      ENNReal.ofReal (A * (((2 : ℝ) ^ (J + j)) ^ (-δ) * ((2 : ℝ) ^ (J + j)) ^ σ)) * F) :
    eLpNorm (fun x ↦ a x + ∑ j ∈ Finset.range N, T j x) p μ ≤
      ENNReal.ofReal (B + A * (1 - (2 : ℝ) ^ (σ - δ))⁻¹) * F := by
  let w (j : ℕ) : ℝ := ((2 : ℝ) ^ (J + j)) ^ (-δ) * ((2 : ℝ) ^ (J + j)) ^ σ
  have hw (j : ℕ) : 0 ≤ w j := by dsimp [w]; positivity
  have hs : eLpNorm (fun x ↦ ∑ j ∈ Finset.range N, T j x) p μ ≤
      ∑ j ∈ Finset.range N, eLpNorm (T j) p μ := by
    have he : (∑ j ∈ Finset.range N, T j) = fun x ↦ ∑ j ∈ Finset.range N, T j x := by
      funext x
      simp only [Finset.sum_apply]
    rw [← he]
    exact eLpNorm_sum_le hp
  have hsum : (∑ j ∈ Finset.range N, eLpNorm (T j) p μ) ≤
      ENNReal.ofReal (A * (1 - (2 : ℝ) ^ (σ - δ))⁻¹) * F := by
    calc
      _ ≤ ∑ j ∈ Finset.range N, ENNReal.ofReal (A * w j) * F :=
        Finset.sum_le_sum (fun j _ ↦ hT j)
      _ = ENNReal.ofReal (A * (∑ j ∈ Finset.range N, w j)) * F := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ mul_nonneg hA (hw j)),
          ← Finset.mul_sum]
      _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (sum_dyadic_rpow_product_le hgap J N) hA)) le_rfl
  calc
    _ ≤ eLpNorm a p μ + eLpNorm (fun x ↦ ∑ j ∈ Finset.range N, T j x) p μ := eLpNorm_add_le hp
    _ ≤ ENNReal.ofReal B * F + ENNReal.ofReal (A * (1 - (2 : ℝ) ^ (σ - δ))⁻¹) * F :=
      add_le_add ha (hs.trans hsum)
    _ = _ := by
      rw [← add_mul, ← ENNReal.ofReal_add hB (mul_nonneg hA (dyadic_rpow_sum_constant_pos hgap).le)]

end OAI.Analysis.Fourier.BochnerRiesz
