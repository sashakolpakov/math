import OAI.Analysis.Fourier.Restriction.Sparse.Gram
import OAI.Analysis.Fourier.Restriction.KernelLp

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem sparse_integralKernel_bound {n : ℕ} (hn : 2 ≤ n)
    (u : SchwartzMap (Space n) ℂ)
    (hu : ∀ ξ, ‖OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ‖ ≤ 1)
    (hr : ∀ ξ, star (OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ) = OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ)
    (hs : ∀ ξ, 1 / 8 ≤ ‖ξ‖ → OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ = 0)
    {p : ℝ} (hp : 1 < p) (hp2 : p < 2) {V : ℝ≥0∞} (hV : V ≠ ⊤) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (N : ℕ) (R : ℝ), 1 ≤ R →
      ∀ z : Fin N → Space n,
      (∀ i j, i ≠ j → R ^ (16 * n) * (N : ℝ) ^ (16 * n) ≤ dist (z i) (z j)) →
      ∀ ν : Measure (Space n), IsFiniteMeasure ν → ν ≤ volume → ν univ ≤ V →
      ∀ f : Fin N × Space n → ℂ, Measurable f → Integrable f (Measure.count.prod ν) →
      eLpNorm (integralKernel (Measure.count.prod ν) (indexedLocalizedKernel u R z) f)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      C * ENNReal.ofReal R ^ (1 / p) * eLpNorm f (ENNReal.ofReal p) (Measure.count.prod ν) := by
  obtain ⟨a, ha, Ha⟩ := localizedFourierKernel_column (by omega : 1 ≤ n) u hu hs
  obtain ⟨b, d, hb, hd, Hb⟩ := indexedLocalizedKernel_gram_bound hn u hu hr hs
  let E := volume (ball (0 : Space n) 1) * ENNReal.ofReal b + ENNReal.ofReal d * V
  let Q := ENNReal.ofReal a * ENNReal.ofReal (p / (p - 1)) + E * ENNReal.ofReal (p / (2 - p))
  let C := 2 * Q ^ (1 / p)
  have hE : E ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top
    (measure_ball_lt_top : volume (ball (0 : Space n) 1) < ⊤).ne ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV⟩
  have hQ : Q ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top, ENNReal.mul_ne_top hE ENNReal.ofReal_ne_top⟩
  refine ⟨C, ENNReal.mul_ne_top (by norm_num) (ENNReal.rpow_ne_top_of_nonneg (by positivity) hQ), ?_⟩
  intro N R hR z hsep ν hνfinite hν hνV f hfm hfi
  let := hνfinite
  have hR0 : 0 < R := by linarith
  have hRE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal R := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hR
  have hcol (x : Fin N × Space n) :
      (∫⁻ ω, ‖indexedLocalizedKernel u R z (ω, x)‖ₑ ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      ENNReal.ofReal a * ENNReal.ofReal R := by
    simpa only [indexedLocalizedKernel, ENNReal.ofReal_mul ha.le] using Ha R hR0 (z x.1) x.2
  have hgram (x : Fin N × Space n) :
      (∫⁻ y, ‖gramKernel (OAI.Analysis.Fourier.Restriction.sphereMeasure n) (indexedLocalizedKernel u R z) (x, y)‖ₑ
        ∂(Measure.count.prod ν)) ≤ E * ENNReal.ofReal R := by
    apply (Hb N R hR z hsep ν inferInstance hν x).trans
    rw [ENNReal.ofReal_mul hb.le]
    dsimp [E]
    rw [add_mul, mul_assoc]
    apply add_le_add le_rfl
    calc
      _ ≤ ENNReal.ofReal d * V := mul_le_mul' le_rfl hνV
      _ ≤ (ENNReal.ofReal d * V) * ENNReal.ofReal R := by
        simpa only [mul_one] using mul_le_mul' (le_rfl : ENNReal.ofReal d * V ≤ _) hRE
  have H := eLpNorm_integralKernel_le (Measure.count.prod ν) (OAI.Analysis.Fourier.Restriction.sphereMeasure n)
    (measurable_indexedLocalizedKernel u hR0 z) (pow_nonneg hR0.le n)
    (norm_indexedLocalizedKernel_le u hu hR0 z) hcol hgram hfm hfi hp hp2
  have he : (ENNReal.ofReal a * ENNReal.ofReal R) * ENNReal.ofReal (p / (p - 1)) +
      (E * ENNReal.ofReal R) * ENNReal.ofReal (p / (2 - p)) = Q * ENNReal.ofReal R := by
    dsimp [Q]
    ring
  rw [he, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)] at H
  simpa only [C, mul_assoc] using H

end OAI.Analysis.Fourier.Restriction
