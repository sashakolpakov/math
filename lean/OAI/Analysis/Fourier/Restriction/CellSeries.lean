import OAI.Analysis.Fourier.Restriction.Cell

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Filter
open scoped ENNReal BigOperators Topology
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem summable_unitCell_integrals {n : ℕ} {f : Space n → ℂ} (hf : Integrable f) :
    Summable (fun k : Fin n → ℤ ↦ ∫ y in OAI.Analysis.Fourier.WavePackets.unitCell n,
      f (OAI.Analysis.Fourier.WavePackets.integerVector k + y)) := by
  have H : (∑' k : Fin n → ℤ, ‖∫ y in OAI.Analysis.Fourier.WavePackets.unitCell n,
      f (OAI.Analysis.Fourier.WavePackets.integerVector k + y)‖ₑ) ≤ ∫⁻ x, ‖f x‖ₑ := by
    calc
      _ ≤ ∑' k : Fin n → ℤ, ∫⁻ y in OAI.Analysis.Fourier.WavePackets.unitCell n,
          ‖f (OAI.Analysis.Fourier.WavePackets.integerVector k + y)‖ₑ := by
        exact ENNReal.tsum_le_tsum (fun k ↦ enorm_integral_le_lintegral_enorm _)
      _ = _ := (OAI.Analysis.Fourier.WavePackets.lintegral_eq_tsum_unitCell (fun x ↦ ‖f x‖ₑ)).symm
  exact (tsum_enorm_ne_top_iff_summable_norm.mp
    (ne_of_lt (H.trans_lt hf.hasFiniteIntegral))).of_norm

theorem hasSum_unitCell_integrals {n : ℕ} {f : Space n → ℂ} (hf : Integrable f) :
    HasSum (fun k : Fin n → ℤ ↦ ∫ y in OAI.Analysis.Fourier.WavePackets.unitCell n,
      f (OAI.Analysis.Fourier.WavePackets.integerVector k + y)) (∫ x, f x) := by
  rw [OAI.Analysis.Fourier.WavePackets.integral_eq_tsum_unitCell hf]
  exact (summable_unitCell_integrals hf).hasSum

end OAI.Analysis.Fourier.Restriction
