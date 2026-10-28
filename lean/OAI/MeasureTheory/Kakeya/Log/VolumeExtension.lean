import OAI.MeasureTheory.Kakeya.Log.Volume
import OAI.MeasureTheory.Kakeya.Log.Overlap

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal BigOperators

noncomputable section
namespace OAI.MeasureTheory.Kakeya

/-- A logarithmic critical extension estimate gives the logarithmic tube-union
volume bound. The extension estimate is needed only out to radius `4/δ²`.
All geometric constants are uniform over the tube family and the scale. -/
theorem local_critical_extension_logarithmic_tube_volume
    {n : ℕ} (hn : 2 ≤ n) (C : ℝ) (hC : 0 < C) (A : ℕ)
    (hext : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ g : Space n → ℂ, MemLp g (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) →
        MemLp (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))
          (volume.restrict (Metric.ball (0 : Space n) (4 / δ ^ 2))) ∧
        eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))
          (volume.restrict (Metric.ball (0 : Space n) (4 / δ ^ 2))) ≤
          ENNReal.ofReal (C * (1 + Real.log (1 / δ)) ^ A) *
            eLpNorm g (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ (v x : Fin m → Space n), (∀ i, ‖v i‖ = 1) → (∀ i, ‖x i‖ ≤ 1) →
        (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) →
      c * ((m : ℝ) * δ ^ (n - 1)) / (1 + Real.log (1 / δ)) ^ (2 * n * A) ≤
        volume.real (tubeUnion δ v x) := by
  obtain ⟨B, hB, Hoverlap⟩ := local_critical_extension_tube_overlap hn
  obtain ⟨c, hc, Hvolume⟩ := tubeUnion_logarithmic_volume_lower n hn
    (B * C ^ 2) (mul_pos hB (sq_pos_of_pos hC)) (2 * A)
  refine ⟨c, hc, ?_⟩
  intro m δ hδ hδone v x hv hx hsep
  have hlog : 0 ≤ 1 + Real.log (1 / δ) := by
    have := Real.log_nonneg ((one_le_div hδ).mpr hδone)
    linarith
  have h := Hoverlap m δ (C * (1 + Real.log (1 / δ)) ^ A) hδ hδone
    (mul_nonneg hC.le (pow_nonneg hlog _)) (hext δ hδ hδone)
    v x hv hx hsep (fun _ ↦ 1) (fun _ ↦ zero_le_one)
  have hcoeff : B * (C * (1 + Real.log (1 / δ)) ^ A) ^ 2 =
      B * C ^ 2 * (1 + Real.log (1 / δ)) ^ (2 * A) := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm A 2]
    ring
  rw [hcoeff] at h
  have hnorm : (∫ y, tubeOverlap δ v x (fun _ ↦ 1) y ^ ((n : ℝ) / ((n : ℝ) - 1))) ^
      (1 / ((n : ℝ) / ((n : ℝ) - 1))) ≤
      B * C ^ 2 * (1 + Real.log (1 / δ)) ^ (2 * A) *
        ((m : ℝ) * δ ^ (n - 1)) ^ (1 / ((n : ℝ) / ((n : ℝ) - 1))) := by
    simpa only [Real.one_rpow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, mul_comm (δ ^ (n - 1)) (m : ℝ)] using h
  have H := Hvolume m δ hδ hδone v x hv hnorm
  have hpow : n * (2 * A) = 2 * n * A := by ring
  simpa only [hpow] using H

end OAI.MeasureTheory.Kakeya
