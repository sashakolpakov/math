import OAI.Analysis.Fourier.SquareFunction.CommonSharp

open OAI.Analysis.Fourier.Wave

/-! The common-input Littlewood–Paley bound. Only a uniform aggregate L²
estimate and the actual differentiated kernel bounds remain as hypotheses.
For annular Fourier projections the L² hypothesis follows from overlap. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set
open scoped ENNReal

noncomputable def commonInputEnvelopeConstant (n : ℕ) (p q C : ℝ) (B : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (scaleKernelConstant n q q C 0) * maximalLpConstant n p +
    (B * cubeBallRatio n ^ (1 / 2 : ℝ)) * squareMaximalLpConstant n p +
    ENNReal.ofReal (scaleKernelConstant n q (q - 1) C 1) * maximalLpConstant n p

noncomputable def commonInputLpConstant (n : ℕ) (p q C : ℝ) (B : ℝ≥0∞) : ℝ≥0∞ :=
  sharpLpConstant n p * commonInputEnvelopeConstant n p q C B

theorem commonInputLpConstant_ne_top {n : ℕ} {p q C : ℝ} {B : ℝ≥0∞}
    (hp : 2 < p) (hB : B ≠ ∞) : commonInputLpConstant n p q C B ≠ ∞ := by
  have hp0 : 0 < p := by linarith
  have hm : maximalLpConstant n p ≠ ∞ := ENNReal.mul_ne_top (by norm_num)
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
  have hs : squareMaximalLpConstant n p ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity)
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by norm_num)) ENNReal.ofReal_ne_top)
  have hd : cubeBallRatio n ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (cubeBallRatio_lt_top n).ne
  have ht : sharpLpConstant n p ≠ ∞ := ENNReal.mul_ne_top (by norm_num)
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)
  exact ENNReal.mul_ne_top ht (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm, ENNReal.mul_ne_top (ENNReal.mul_ne_top hB hd) hs⟩,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm⟩)

theorem measurable_commonInputEnvelope {n : ℕ} (f : Space n → ℂ) (q C : ℝ) (B : ℝ≥0∞) :
    Measurable (commonInputEnvelope f q C B) := by
  have hm := measurable_ballMaximal volume (fun y => ‖f y‖ₑ)
  have hs : Measurable (fun z => B * (cubeBallRatio n *
      ballMaximal volume (fun y => ‖f y‖ₑ ^ (2 : ℝ)) z) ^ (1 / 2 : ℝ)) :=
    (((measurable_ballMaximal volume _).const_mul _).pow_const _).const_mul _
  exact ((hm.const_mul _).add hs).add (hm.const_mul _)

theorem commonInputEnvelope_ne_top {n : ℕ} (f : Space n → ℂ)
    (hfb : BddAbove (range fun x => ‖f x‖)) (q C : ℝ) {B : ℝ≥0∞}
    (hB : B ≠ ∞) (z : Space n) : commonInputEnvelope f q C B z ≠ ∞ := by
  have hm : ballMaximal volume (fun y => ‖f y‖ₑ) z ≠ ∞ := by
    simpa only [ofReal_norm] using ballMaximal_ofReal_ne_top_of_bounded hfb z
  have hs := ballMaximal_enorm_sq_ne_top hfb z
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm,
      ENNReal.mul_ne_top hB (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
        (ENNReal.mul_ne_top (cubeBallRatio_lt_top n).ne hs))⟩,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm⟩

theorem eLpNorm_commonInputEnvelope_le {n : ℕ} (f : Space n → ℂ)
    (hf : Measurable f) {p : ℝ} (hp : 2 < p) (q C : ℝ) (B : ℝ≥0∞) :
    eLpNorm (commonInputEnvelope f q C B) (ENNReal.ofReal p) volume ≤
      commonInputEnvelopeConstant n p q C B * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
  let M := ballMaximal volume (fun y => ‖f y‖ₑ)
  let V := fun x => ballMaximal volume (fun y => ‖f y‖ₑ ^ (2 : ℝ)) x ^ (1 / 2 : ℝ)
  let A := ENNReal.ofReal (scaleKernelConstant n q q C 0)
  let E := B * cubeBallRatio n ^ (1 / 2 : ℝ)
  let T := ENNReal.ofReal (scaleKernelConstant n q (q - 1) C 1)
  have hM : Measurable M := measurable_ballMaximal volume _
  have hV : Measurable V := (measurable_ballMaximal volume _).pow_const _
  have hMl : eLpNorm M (ENNReal.ofReal p) volume ≤
      maximalLpConstant n p * eLpNorm f (ENNReal.ofReal p) volume := by
    simpa only [M, maximalLpConstant, ofReal_norm, eLpNorm_norm f hf.aestronglyMeasurable] using
      eLpNorm_euclidean_ballMaximal_le (n := n) hf.norm (fun x => norm_nonneg (f x)) (by linarith : 1 < p)
  have hVl : eLpNorm V (ENNReal.ofReal p) volume ≤
      squareMaximalLpConstant n p * eLpNorm f (ENNReal.ofReal p) volume := by
    simpa only [V, squareMaximalLpConstant, ofReal_norm_sq, eLpNorm_norm f hf.aestronglyMeasurable] using
      eLpNorm_square_maximal_le (n := n) hf.norm (fun x => norm_nonneg (f x)) hp
  have he : commonInputEnvelope f q C B = fun x => A * M x + 0 + E * V x + T * M x := by
    funext x
    dsimp only [commonInputEnvelope, A, M, E, V, T]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    simp only [add_zero, mul_assoc]
  rw [he]
  apply (eLpNorm_ennreal_four_add_le volume _ _ _ _ hp1).trans
  rw [eLpNorm_ennreal_const_mul volume hM A hp0,
    eLpNorm_ennreal_const_mul volume hV E hp0, eLpNorm_ennreal_const_mul volume hM T hp0]
  have hz : eLpNorm (fun _ : Space n => (0 : ℝ≥0∞)) (ENNReal.ofReal p) volume = 0 := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top
      measurable_const.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofReal hp0.le, enorm_eq_self,
      ENNReal.zero_rpow_of_pos hp0, lintegral_zero,
      ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp0)]
  rw [hz, add_zero]
  calc
    _ ≤ A * (maximalLpConstant n p * eLpNorm f (ENNReal.ofReal p) volume) +
        E * (squareMaximalLpConstant n p * eLpNorm f (ENNReal.ofReal p) volume) +
        T * (maximalLpConstant n p * eLpNorm f (ENNReal.ofReal p) volume) :=
      add_le_add (add_le_add (mul_le_mul_right hMl _) (mul_le_mul_right hVl _)) (mul_le_mul_right hMl _)
    _ = _ := by dsimp only [commonInputEnvelopeConstant, A, E, T]; ring

/-- A finite family of dyadic kernels with a uniform aggregate L² bound
has a uniform common-input Lᵖ square-function bound, for every `p > 2`.
The constant is independent of the number and location of scales. -/
theorem littlewoodPaley_kernel_family {n : ℕ} [NeZero n] {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (s : Finset ℤ) (K : s → Space n → H) (f : Space n → ℂ)
    {p q C : ℝ} (hp : 2 < p) (hq : (n : ℝ) + 1 < q) (hC : 0 ≤ C)
    (hKd : ∀ i, Differentiable ℝ (K i))
    (hK : ∀ i u, ‖K i u‖ ≤ C * ((2 : ℝ) ^ i.val) ^ n *
      ((2 : ℝ) ^ i.val * ‖u‖ + 1) ^ (-q))
    (hK' : ∀ i u, ‖fderiv ℝ (K i) u‖ ≤ C * (((2 : ℝ) ^ i.val) ^ n * (2 : ℝ) ^ i.val) *
      ((2 : ℝ) ^ i.val * ‖u‖ + 1) ^ (-q))
    (hfm : Measurable f) (hfi : Integrable f) (hfb : BddAbove (range fun x => ‖f x‖))
    (hf2 : MemLp f 2 volume) {B : ℝ≥0∞} (hB : B ≠ ∞)
    (h2 : ∀ (g : Space n → ℂ), Integrable g → MemLp g 2 volume →
      eLpNorm (fun x => vectorNorm (fun i => convolveKernel (K i) g x)) 2 volume ≤ B * eLpNorm g 2 volume) :
    eLpNorm (fun x => vectorNorm (fun i => convolveKernel (K i) f x)) (ENNReal.ofReal p) volume ≤
      commonInputLpConstant n p q C B * eLpNorm f (ENNReal.ofReal p) volume := by
  have hq0 : 0 ≤ q := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hKB (i : s) : BddAbove (range fun x => ‖K i x‖) := by
    refine ⟨C * ((2 : ℝ) ^ i.val) ^ n, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact bounded_of_polynomial_decay (by positivity) hq0 hC (hK i) x
  have hKi (i : s) : Integrable (K i) := integrable_of_polynomial_decay
    (by positivity) (by linarith : (n : ℝ) < q) (hKd i).continuous.aestronglyMeasurable (hK i)
  have huc (i : s) : Continuous (convolveKernel (K i) f) :=
    continuous_convolveKernel hfi (hKd i).continuous (hKB i)
  have hui (i : s) : Integrable (convolveKernel (K i) f) := integrable_convolveKernel hfi (hKi i)
  have hM (z : Space n) : ballMaximal volume (fun y => ‖f y‖ₑ) z ≠ ∞ := by
    simpa only [ofReal_norm] using ballMaximal_ofReal_ne_top_of_bounded hfb z
  have hos := common_input_cube_oscillation s K f hq hC hKd hK hK' hfm hfi hf2 h2 hM
  have hsharp := eLpNorm_le_of_centered_envelope
    (fun x => vectorNorm (fun i => convolveKernel (K i) f x))
    (commonInputEnvelope f q C B) (fun _ => vectorNorm_nonneg _)
    (continuous_vectorNorm _ huc) (integrable_vectorNorm volume _ huc hui)
    (measurable_commonInputEnvelope f q C B) (commonInputEnvelope_ne_top f hfb q C hB)
    (by linarith : 1 < p) (sharpParameter_pos n p) (sharpParameter_small n p) hos
  have hnorm := eLpNorm_commonInputEnvelope_le f hfm hp q C B
  exact hsharp.trans (by
    change sharpLpConstant n p * _ ≤ _
    simpa only [commonInputLpConstant, mul_assoc] using mul_le_mul_right hnorm (sharpLpConstant n p))

end OAI.Analysis.Fourier.SquareFunction
