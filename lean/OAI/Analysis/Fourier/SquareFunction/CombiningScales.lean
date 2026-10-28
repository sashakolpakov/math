import OAI.Analysis.Fourier.SquareFunction.CombiningEnvelopes

open OAI.Analysis.Fourier.Wave

/-! The finite combining-scales estimate, with all sharp-function and
maximal estimates discharged. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set
open scoped ENNReal

noncomputable def sharpParameter (n : ℕ) (p : ℝ) : ℝ :=
  (2 * (((2 : ℝ) ^ n + 1) ^ p))⁻¹

noncomputable def sharpLpConstant (n : ℕ) (p : ℝ) : ℝ≥0∞ :=
  2 * ((ENNReal.ofReal (1 / (1 - sharpParameter n p * ((2 : ℝ) ^ n + 1) ^ p))) ^ (1 / p) *
    ENNReal.ofReal (((2 : ℝ) ^ n + 1) / sharpParameter n p))

theorem sharpParameter_pos (n : ℕ) (p : ℝ) : 0 < sharpParameter n p := by
  unfold sharpParameter
  positivity

theorem sharpParameter_small (n : ℕ) (p : ℝ) :
    sharpParameter n p * ((2 : ℝ) ^ n + 1) ^ p < 1 := by
  have ha : 0 < ((2 : ℝ) ^ n + 1) ^ p := by positivity
  have he : sharpParameter n p * ((2 : ℝ) ^ n + 1) ^ p = 1 / 2 := by
    unfold sharpParameter
    field_simp
  rw [he]
  norm_num

/-- A family of kernels at dyadic scales obeys the finite vector estimate.
Only the scalar `L²` and `Lᵖ` bounds and the stated first-derivative decay are
assumed. The constant is independent of the finite set of scales. -/
theorem combining_scale_family {n : ℕ} [NeZero n] {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (s : Finset ℤ) (K : s → Space n → H) (f : s → Space n → ℂ)
    {p q C : ℝ} (hp : 2 < p) (hq : (n : ℝ) + 1 < q) (hC : 0 ≤ C)
    (hKd : ∀ i, Differentiable ℝ (K i))
    (hK : ∀ i u, ‖K i u‖ ≤ C * ((2 : ℝ) ^ i.val) ^ n *
      ((2 : ℝ) ^ i.val * ‖u‖ + 1) ^ (-q))
    (hK' : ∀ i u, ‖fderiv ℝ (K i) u‖ ≤ C * (((2 : ℝ) ^ i.val) ^ n * (2 : ℝ) ^ i.val) *
      ((2 : ℝ) ^ i.val * ‖u‖ + 1) ^ (-q))
    (hfm : ∀ i, Measurable (f i)) (hfi : ∀ i, Integrable (f i))
    (hfb : ∀ i, BddAbove (range fun x => ‖f i x‖))
    (hf2 : ∀ i, MemLp (f i) 2 volume) {B₂ Bₚ : ℝ≥0∞} (hB₂ : B₂ ≠ ∞)
    (h2 : ∀ i (g : Space n → ℂ), Integrable g → MemLp g 2 volume →
      eLpNorm (convolveKernel (K i) g) 2 volume ≤ B₂ * eLpNorm g 2 volume)
    (hBₚ : ∀ i, eLpNorm (convolveKernel (K i) (f i)) (ENNReal.ofReal p) volume ≤
      Bₚ * eLpNorm (f i) (ENNReal.ofReal p) volume)
    {L : ℤ} (hL : 0 < L) :
    eLpNorm (fun x => vectorNorm (fun i => convolveKernel (K i) (f i) x))
      (ENNReal.ofReal p) volume ≤
      (sharpLpConstant n p * convolutionEnvelopeConstant n p q C B₂ Bₚ L) *
        eLpNorm (fun x => vectorNorm (fun i => f i x)) (ENNReal.ofReal p) volume := by
  have hq0 : 0 ≤ q := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hKb (i : s) : ∀ x, ‖K i x‖ ≤ C * ((2 : ℝ) ^ i.val) ^ n :=
    bounded_of_polynomial_decay (by positivity) hq0 hC (hK i)
  have hKB (i : s) : BddAbove (range fun x => ‖K i x‖) :=
    ⟨_, by rintro _ ⟨x, rfl⟩; exact hKb i x⟩
  have hKi (i : s) : Integrable (K i) := integrable_of_polynomial_decay
    (by positivity) (by linarith : (n : ℝ) < q) (hKd i).continuous.aestronglyMeasurable (hK i)
  have huc (i : s) : Continuous (convolveKernel (K i) (f i)) :=
    continuous_convolveKernel (hfi i) (hKd i).continuous (hKB i)
  have hui (i : s) : Integrable (convolveKernel (K i) (f i)) := integrable_convolveKernel (hfi i) (hKi i)
  have hub (i : s) : BddAbove (range fun x => ‖convolveKernel (K i) (f i) x‖) := by
    refine ⟨(∫ y, ‖f i y‖) * (C * ((2 : ℝ) ^ i.val) ^ n), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact norm_convolveKernel_le (hfi i) (hKd i).continuous (hKb i) x
  have hM (z : Space n) : ballMaximal volume
      (fun y => ENNReal.ofReal (vectorNorm (fun i => f i y))) z ≠ ∞ :=
    ballMaximal_ofReal_ne_top_of_bounded (bounded_vectorNorm f hfb) z
  have hos := convolution_cube_oscillation s K f hp.le hq hC hKd hK hK' hfm hfi hf2 h2 hL hM
  have hsharp := eLpNorm_le_of_centered_envelope
    (fun x => vectorNorm (fun i => convolveKernel (K i) (f i) x))
    (convolutionEnvelope s K f p q C B₂ L) (fun x => vectorNorm_nonneg _)
    (continuous_vectorNorm _ huc) (integrable_vectorNorm volume _ huc hui)
    (measurable_convolutionEnvelope s K f p q C B₂ L)
    (convolutionEnvelope_ne_top s K f hfb hub hp q C hB₂ L)
    (by linarith : 1 < p) (sharpParameter_pos n p) (sharpParameter_small n p) hos
  have hnorm := eLpNorm_convolutionEnvelope_le s K f (fun i => (huc i).measurable) hfm
    hp q C B₂ Bₚ L hBₚ
  exact hsharp.trans (by
    change sharpLpConstant n p * _ ≤ _
    simpa only [mul_assoc] using mul_le_mul_right hnorm (sharpLpConstant n p))

end OAI.Analysis.Fourier.SquareFunction
