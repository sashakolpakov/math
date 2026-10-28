import OAI.Analysis.Fourier.Restriction.KernelL2
import OAI.Analysis.Fourier.Restriction.OperatorInterpolation

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- The sparse-summation kernel criterion: a column `L¹` estimate and a
Schur bound for the actual Gram kernel imply the full intermediate `Lᵖ`
estimate. This includes the `TT*` and interpolation arguments. -/
theorem eLpNorm_integralKernel_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y) [IsFiniteMeasure ν]
    {K : Y × X → ℂ} (hK : Measurable K)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ z, ‖K z‖ ≤ M)
    {A B : ℝ≥0∞}
    (hcol : ∀ x, (∫⁻ y, ‖K (y, x)‖ₑ ∂ν) ≤ A)
    (hgram : ∀ x, (∫⁻ z, ‖gramKernel ν K (x, z)‖ₑ ∂μ) ≤ B)
    {f : X → ℂ} (hfm : Measurable f) (hf : Integrable f μ)
    {p : ℝ} (hp : 1 < p) (hp2 : p < 2) :
    eLpNorm (integralKernel μ K f) (ENNReal.ofReal p) ν ≤
      2 * (A * ENNReal.ofReal (p / (p - 1)) + B * ENNReal.ofReal (p / (2 - p))) ^ (1 / p) *
        eLpNorm f (ENNReal.ofReal p) μ := by
  apply eLpNorm_operator_le_of_L1_L2 μ ν (integralKernel μ K)
    (fun g hg ↦ measurable_integralKernel μ hK hg.aestronglyMeasurable)
    (fun g h hg hh y ↦ integralKernel_add μ hK hbound hg hh y)
    (fun g hg ↦ lintegral_integralKernel_le μ ν hK hg.aestronglyMeasurable hcol)
    (fun g hg _ ↦ lintegral_sq_integralKernel_le μ ν hK hM hbound hgram hg) hfm hf hp hp2

end OAI.Analysis.Fourier.Restriction
