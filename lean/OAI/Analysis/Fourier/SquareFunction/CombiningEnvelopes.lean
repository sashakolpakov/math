import OAI.Analysis.Fourier.SquareFunction.CubeOscillation
import OAI.Analysis.Fourier.SquareFunction.EnvelopeLp

open OAI.Analysis.Fourier.Wave

/-! Global bounds for the four actual envelopes in the combining-dilates
argument. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set
open scoped ENNReal

noncomputable def maximalLpConstant (n : ℕ) (p : ℝ) : ℝ≥0∞ :=
  2 * ENNReal.ofReal ((5 : ℝ) ^ n * p / (p - 1)) ^ (1 / p)

noncomputable def squareMaximalLpConstant (n : ℕ) (p : ℝ) : ℝ≥0∞ :=
  ((2 : ℝ≥0∞) ^ (p / 2) * ENNReal.ofReal ((5 : ℝ) ^ n * (p / 2) / (p / 2 - 1))) ^ (1 / p)

noncomputable def convolutionEnvelopeConstant (n : ℕ) (p q C : ℝ)
    (B₂ Bₚ : ℝ≥0∞) (L : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (scaleKernelConstant n q q C L) * maximalLpConstant n p +
    (cubeBallRatio n ^ (1 / 2 : ℝ) * ((2 * L).toNat : ℝ≥0∞) ^ (1 / 2 - 1 / p)) *
      (squareMaximalLpConstant n p * Bₚ) +
    (B₂ * cubeBallRatio n ^ (1 / 2 : ℝ)) * squareMaximalLpConstant n p +
    ENNReal.ofReal (scaleKernelConstant n q (q - 1) C L) * maximalLpConstant n p

theorem ofReal_norm_sq {H : Type*} [NormedAddCommGroup H] (v : H) :
    ENNReal.ofReal (‖v‖ ^ 2) = ‖v‖ₑ ^ (2 : ℝ) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.rpow_two]

theorem eLpNorm_vector_middle_envelope {n : ℕ} {I H : Type*} [Fintype I]
    [NormedAddCommGroup H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (u : I → Space n → H) (f : I → Space n → ℂ)
    (hu : ∀ i, Measurable (u i)) (hf : ∀ i, Measurable (f i)) {p : ℝ} (hp : 2 < p)
    {B : ℝ≥0∞} (hB : ∀ i, eLpNorm (u i) (ENNReal.ofReal p) volume ≤
      B * eLpNorm (f i) (ENNReal.ofReal p) volume) :
    eLpNorm (fun x => (∑ i, ballMaximal volume (fun y => ‖u i y‖ₑ ^ (2 : ℝ)) x ^
      (p / 2)) ^ (1 / p)) (ENNReal.ofReal p) volume ≤
      (squareMaximalLpConstant n p * B) *
        eLpNorm (fun x => vectorNorm (fun i => f i x)) (ENNReal.ofReal p) volume := by
  have h := eLpNorm_middle_envelope_le Finset.univ (fun i x => ‖u i x‖) (fun i x => ‖f i x‖)
    (fun i _ => (hu i).norm) (fun i _ x => norm_nonneg _) (fun i _ => (hf i).norm)
    (fun i _ x => norm_nonneg _) hp (B := B) (fun i _ => ?_)
  · simp only [ofReal_norm_sq, ofReal_norm, ← ofReal_vectorNorm] at h
    rwa [eLpNorm_ofReal_eq volume (measurable_vectorNorm f hf) (fun x => vectorNorm_nonneg _)] at h
  · rw [eLpNorm_norm _ (hu i).aestronglyMeasurable, eLpNorm_norm _ (hf i).aestronglyMeasurable]
    exact hB i

theorem measurable_convolutionEnvelope {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (s : Finset ℤ) (K : s → Space n → H) (f : s → Space n → ℂ)
    (p q C : ℝ) (B : ℝ≥0∞) (L : ℤ) :
    Measurable (convolutionEnvelope s K f p q C B L) := by
  have hm := measurable_ballMaximal volume (fun y => ENNReal.ofReal (vectorNorm (fun i => f i y)))
  have hmid : Measurable (fun z => (∑ i,
      ballMaximal volume (fun y => ‖convolveKernel (K i) (f i) y‖ₑ ^ (2 : ℝ)) z ^ (p / 2)) ^ (1 / p)) :=
    (Finset.measurable_sum _ (fun i _ => (measurable_ballMaximal volume _).pow_const _)).pow_const _
  have hhi : Measurable (fun z => B * (cubeBallRatio n *
      ballMaximal volume (fun y => ∑ i, ‖f i y‖ₑ ^ (2 : ℝ)) z) ^ (1 / 2 : ℝ)) :=
    (((measurable_ballMaximal volume _).const_mul _).pow_const _).const_mul _
  exact (((hm.const_mul _).add (hmid.const_mul _)).add hhi).add (hm.const_mul _)

theorem eLpNorm_convolutionEnvelope_le {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (s : Finset ℤ) (K : s → Space n → H) (f : s → Space n → ℂ)
    (hu : ∀ i, Measurable (convolveKernel (K i) (f i))) (hf : ∀ i, Measurable (f i))
    {p : ℝ} (hp : 2 < p) (q C : ℝ) (B₂ Bₚ : ℝ≥0∞) (L : ℤ)
    (hBₚ : ∀ i, eLpNorm (convolveKernel (K i) (f i)) (ENNReal.ofReal p) volume ≤
      Bₚ * eLpNorm (f i) (ENNReal.ofReal p) volume) :
    eLpNorm (convolutionEnvelope s K f p q C B₂ L) (ENNReal.ofReal p) volume ≤
      convolutionEnvelopeConstant n p q C B₂ Bₚ L *
        eLpNorm (fun x => vectorNorm (fun i => f i x)) (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
  let W := fun x => vectorNorm (fun i => f i x)
  let M := ballMaximal volume (fun y => ENNReal.ofReal (W y))
  let F := fun x => (∑ i, ballMaximal volume (fun y => ‖convolveKernel (K i) (f i) y‖ₑ ^ (2 : ℝ)) x ^
    (p / 2)) ^ (1 / p)
  let V := fun x => ballMaximal volume (fun y => ENNReal.ofReal ((W y) ^ 2)) x ^ (1 / 2 : ℝ)
  let A := ENNReal.ofReal (scaleKernelConstant n q q C L)
  let D := cubeBallRatio n ^ (1 / 2 : ℝ) * ((2 * L).toNat : ℝ≥0∞) ^ (1 / 2 - 1 / p)
  let E := B₂ * cubeBallRatio n ^ (1 / 2 : ℝ)
  let T := ENNReal.ofReal (scaleKernelConstant n q (q - 1) C L)
  have hW : Measurable W := measurable_vectorNorm f hf
  have hM : Measurable M := measurable_ballMaximal volume _
  have hF : Measurable F :=
    (Finset.measurable_sum _ (fun i _ => (measurable_ballMaximal volume _).pow_const _)).pow_const _
  have hV : Measurable V := (measurable_ballMaximal volume _).pow_const _
  have hMl := eLpNorm_euclidean_ballMaximal_le hW (fun x => vectorNorm_nonneg _) (by linarith : 1 < p)
  have hFl := eLpNorm_vector_middle_envelope (fun i => convolveKernel (K i) (f i)) f hu hf hp hBₚ
  have hVl := eLpNorm_square_maximal_le hW (fun x => vectorNorm_nonneg _) hp
  have hw₂ (y : Space n) : ENNReal.ofReal ((vectorNorm (fun i => f i y)) ^ 2) =
      ∑ i, ‖f i y‖ₑ ^ (2 : ℝ) := by
    rw [ENNReal.ofReal_pow (vectorNorm_nonneg _), ← ENNReal.rpow_two, enorm_vectorNorm_sq]
  have he : convolutionEnvelope s K f p q C B₂ L = fun x => A * M x + D * F x + E * V x + T * M x := by
    funext x
    dsimp only [convolutionEnvelope, A, M, D, F, E, V, T, W]
    simp_rw [hw₂]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_assoc]
    ac_rfl
  rw [he]
  apply (eLpNorm_ennreal_four_add_le volume _ _ _ _ hp1).trans
  rw [eLpNorm_ennreal_const_mul volume hM A hp0, eLpNorm_ennreal_const_mul volume hF D hp0,
    eLpNorm_ennreal_const_mul volume hV E hp0, eLpNorm_ennreal_const_mul volume hM T hp0]
  calc
    _ ≤ A * (maximalLpConstant n p * eLpNorm W (ENNReal.ofReal p) volume) +
        D * ((squareMaximalLpConstant n p * Bₚ) * eLpNorm W (ENNReal.ofReal p) volume) +
        E * (squareMaximalLpConstant n p * eLpNorm W (ENNReal.ofReal p) volume) +
        T * (maximalLpConstant n p * eLpNorm W (ENNReal.ofReal p) volume) := by
      exact add_le_add (add_le_add (add_le_add (mul_le_mul_right hMl _) (mul_le_mul_right hFl _))
        (mul_le_mul_right hVl _)) (mul_le_mul_right hMl _)
    _ = _ := by dsimp only [convolutionEnvelopeConstant, A, D, E, T, W]; ring

theorem convolutionEnvelope_ne_top {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (s : Finset ℤ) (K : s → Space n → H) (f : s → Space n → ℂ)
    (hfb : ∀ i, BddAbove (range fun x => ‖f i x‖))
    (hub : ∀ i, BddAbove (range fun x => ‖convolveKernel (K i) (f i) x‖))
    {p : ℝ} (hp : 2 < p) (q C : ℝ) {B : ℝ≥0∞} (hB : B ≠ ∞) (L : ℤ) (z : Space n) :
    convolutionEnvelope s K f p q C B L z ≠ ∞ := by
  have hp0 : 0 < p := by linarith
  have hm : ballMaximal volume (fun y => ENNReal.ofReal (vectorNorm (fun i => f i y))) z ≠ ∞ :=
    ballMaximal_ofReal_ne_top_of_bounded (bounded_vectorNorm f hfb) z
  have hmid : (∑ i, ballMaximal volume (fun y => ‖convolveKernel (K i) (f i) y‖ₑ ^ (2 : ℝ)) z ^
      (p / 2)) ^ (1 / p) ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
    apply ENNReal.sum_ne_top.mpr
    intro i hi
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (ballMaximal_enorm_sq_ne_top (hub i) z)
  have hWb : BddAbove (range fun y => ‖vectorNorm (fun i => f i y)‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (vectorNorm_nonneg _)] using bounded_vectorNorm f hfb
  have hm₂ : ballMaximal volume (fun y => ∑ i, ‖f i y‖ₑ ^ (2 : ℝ)) z ≠ ∞ := by
    have h := ballMaximal_enorm_sq_ne_top hWb z
    simpa only [Real.enorm_eq_ofReal (vectorNorm_nonneg _), enorm_vectorNorm_sq] using h
  have hθ : 0 ≤ 1 / 2 - 1 / p := by
    have hdiv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp.le
    linarith
  unfold convolutionEnvelope
  apply ENNReal.add_ne_top.mpr
  constructor
  · apply ENNReal.add_ne_top.mpr
    constructor
    · apply ENNReal.add_ne_top.mpr
      constructor
      · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm
      · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (cubeBallRatio_lt_top n).ne)
          (ENNReal.rpow_ne_top_of_nonneg hθ (by simp))) hmid
    · exact ENNReal.mul_ne_top hB (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
        (ENNReal.mul_ne_top (cubeBallRatio_lt_top n).ne hm₂))
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm

end OAI.Analysis.Fourier.SquareFunction
