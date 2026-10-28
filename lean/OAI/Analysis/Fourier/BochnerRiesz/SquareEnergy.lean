import OAI.Analysis.Fourier.SquareFunction.LocalizedL2

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem eLpNorm_two_eq_energy {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] {μ : Measure X} {f : X → H} (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    hf.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat]
  congr 1
  rw [ofReal_integral_eq_lintegral_ofReal hf.norm.integrable_sq
    (Filter.Eventually.of_forall (fun x ↦ sq_nonneg ‖f x‖))]
  apply lintegral_congr
  intro x
  rw [ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem eLpNorm_vectorNorm_two_eq_energy {X I : Type*} [MeasurableSpace X]
    [Fintype I] {μ : Measure X} (v : I → X → ℂ)
    (hv : ∀ i, Measurable (v i)) (hv2 : ∀ i, MemLp (v i) 2 μ) :
    eLpNorm (fun x ↦ OAI.Analysis.Fourier.SquareFunction.vectorNorm (fun i ↦ v i x)) 2 μ =
      ENNReal.ofReal (∫ x, ∑ i, ‖v i x‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  have hm : AEStronglyMeasurable (fun x ↦ OAI.Analysis.Fourier.SquareFunction.vectorNorm (fun i ↦ v i x)) μ :=
    (OAI.Analysis.Fourier.SquareFunction.measurable_vectorNorm v hv).aestronglyMeasurable
  have hi : Integrable (fun x ↦ ‖OAI.Analysis.Fourier.SquareFunction.vectorNorm (fun i ↦ v i x)‖ ^ 2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs, OAI.Analysis.Fourier.SquareFunction.vectorNorm_sq] using
      (integrable_finsetSum Finset.univ (fun i _ ↦ (hv2 i).norm.integrable_sq))
  have h2 := (memLp_two_iff_integrable_sq_norm hm).mpr hi
  rw [eLpNorm_two_eq_energy h2]
  simp only [Real.norm_eq_abs, sq_abs, OAI.Analysis.Fourier.SquareFunction.vectorNorm_sq]

end OAI.Analysis.Fourier.BochnerRiesz
