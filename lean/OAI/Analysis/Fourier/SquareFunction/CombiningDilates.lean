import OAI.Analysis.Fourier.SquareFunction.DilationNorm

open OAI.Analysis.Fourier.Wave

/-! The source's combining-dilates theorem for actual normalized dilations
of one kernel. The scalar operator bounds are preserved by change of variables. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set
open scoped ENNReal

theorem combining_normalized_dilates {n : ℕ} [NeZero n] {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (s : Finset ℤ) (K : Space n → H) (f : s → Space n → ℂ)
    {p q C δ : ℝ} (hp : 2 < p) (hq : (n : ℝ) + 1 < q) (hC : 0 ≤ C)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hKd : Differentiable ℝ K)
    (hK : ∀ u, ‖K u‖ ≤ (C * δ ^ (-q)) * (‖u‖ + 1) ^ (-q))
    (hK' : ∀ u, ‖fderiv ℝ K u‖ ≤ (C * δ ^ (-q)) * (‖u‖ + 1) ^ (-q))
    (hfm : ∀ i, Measurable (f i)) (hfi : ∀ i, Integrable (f i))
    (hfb : ∀ i, BddAbove (range fun x => ‖f i x‖))
    (hf2 : ∀ i, MemLp (f i) 2 volume)
    (hfp : ∀ i, MemLp (f i) (ENNReal.ofReal p) volume)
    {B₂ Bₚ : ℝ≥0∞} (hB₂ : B₂ ≠ ∞)
    (h2 : ∀ (g : Space n → ℂ), Integrable g → MemLp g 2 volume →
      eLpNorm (convolveKernel K g) 2 volume ≤ B₂ * eLpNorm g 2 volume)
    (hP : ∀ (g : Space n → ℂ), Integrable g → MemLp g (ENNReal.ofReal p) volume →
      eLpNorm (convolveKernel K g) (ENNReal.ofReal p) volume ≤ Bₚ * eLpNorm g (ENNReal.ofReal p) volume) :
    eLpNorm (fun x => vectorNorm (fun i => convolveKernel (dilatedKernel K ((2 : ℝ) ^ i.val)) (f i) x))
      (ENNReal.ofReal p) volume ≤
      (combiningLogConstant n p q *
        (ENNReal.ofReal (C * δ) + ENNReal.ofReal (1 + Real.log (1 / δ)) ^
          (1 / 2 - 1 / p) * Bₚ + B₂)) *
        eLpNorm (fun x => vectorNorm (fun i => f i x)) (ENNReal.ofReal p) volume := by
  apply combining_dyadic_kernels s (fun i => dilatedKernel K ((2 : ℝ) ^ i.val)) f hp hq hC hδ hδ1
    (fun i => differentiable_dilatedKernel hKd _)
    (fun i => dilatedKernel_decay (by positivity) hK)
    (fun i => dilatedKernel_derivative_decay (by positivity) hKd hK')
    hfm hfi hfb hf2 hB₂
  · intro i g hgi hg2
    exact convolve_dilatedKernel_bound K g hgi hg2 h2 (by positivity)
  · intro i
    exact convolve_dilatedKernel_bound K (f i) (hfi i) (hfp i) hP (by positivity)

end OAI.Analysis.Fourier.SquareFunction
