import OAI.Analysis.Fourier.SquareFunction.CubeVectors

open OAI.Analysis.Fourier.Wave

/-! The complete cube oscillation estimate in the combining-dilates lemma.
The hypotheses below are scalar operator bounds and pointwise bounds on the
actual kernels; there is no vector-valued or sharp-function hypothesis. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set Metric
open scoped ENNReal

noncomputable def scaleKernelConstant (n : ℕ) (q r C : ℝ) (L : ℤ) : ℝ :=
  Real.sqrt (4 / 3) * (2 : ℝ) ^ (-L) * (C * 2 ^ q * (polynomialKernelMass n r).toReal)

theorem scaleKernelConstant_nonneg {n : ℕ} {q r C : ℝ} {L : ℤ} (hC : 0 ≤ C) :
    0 ≤ scaleKernelConstant n q r C L := by unfold scaleKernelConstant; positivity

noncomputable def convolutionEnvelope {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (s : Finset ℤ) (K : s → Space n → H) (f : s → Space n → ℂ)
    (p q C : ℝ) (B : ℝ≥0∞) (L : ℤ) (z : Space n) : ℝ≥0∞ :=
  ENNReal.ofReal (scaleKernelConstant n q q C L) *
      ballMaximal volume (fun y => ENNReal.ofReal (vectorNorm (fun i => f i y))) z +
    (cubeBallRatio n ^ (1 / 2 : ℝ) * ((2 * L).toNat : ℝ≥0∞) ^ (1 / 2 - 1 / p)) *
      (∑ i, ballMaximal volume (fun y => ‖convolveKernel (K i) (f i) y‖ₑ ^ (2 : ℝ)) z ^
        (p / 2)) ^ (1 / p) +
    B * (cubeBallRatio n * ballMaximal volume (fun y => ∑ i, ‖f i y‖ₑ ^ (2 : ℝ)) z) ^
      (1 / 2 : ℝ) +
    ENNReal.ofReal (scaleKernelConstant n q (q - 1) C L) *
      ballMaximal volume (fun y => ENNReal.ofReal (vectorNorm (fun i => f i y))) z

theorem convolution_cube_oscillation {n : ℕ} [NeZero n] {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (s : Finset ℤ) (K : s → Space n → H) (f : s → Space n → ℂ)
    {p q C : ℝ} (hp : 2 ≤ p) (hq : (n : ℝ) + 1 < q) (hC : 0 ≤ C)
    (hKd : ∀ i, Differentiable ℝ (K i))
    (hK : ∀ i u, ‖K i u‖ ≤ C * ((2 : ℝ) ^ i.val) ^ n *
      ((2 : ℝ) ^ i.val * ‖u‖ + 1) ^ (-q))
    (hK' : ∀ i u, ‖fderiv ℝ (K i) u‖ ≤ C * (((2 : ℝ) ^ i.val) ^ n * (2 : ℝ) ^ i.val) *
      ((2 : ℝ) ^ i.val * ‖u‖ + 1) ^ (-q))
    (hfm : ∀ i, Measurable (f i)) (hfi : ∀ i, Integrable (f i))
    (hf2 : ∀ i, MemLp (f i) 2 volume) {B : ℝ≥0∞}
    (h2 : ∀ i (g : Space n → ℂ), Integrable g → MemLp g 2 volume →
      eLpNorm (convolveKernel (K i) g) 2 volume ≤ B * eLpNorm g 2 volume)
    {L : ℤ} (hL : 0 < L)
    (hM : ∀ z, ballMaximal volume (fun y => ENNReal.ofReal (vectorNorm (fun i => f i y))) z ≠ ∞)
    (Q : BoxIntegral.Box (Fin n)) (hQ : IsCubeBox Q) :
    ∃ c : ℝ, ∀ z ∈ euclideanBox Q,
      (∫⁻ x in euclideanBox Q, ‖vectorNorm (fun i => convolveKernel (K i) (f i) x) - c‖ₑ) /
        volume (euclideanBox Q) ≤ convolutionEnvelope s K f p q C B L z := by
  classical
  let i₀ : Fin n := Classical.arbitrary (Fin n)
  let d := Q.upper i₀ - Q.lower i₀
  have hd : 0 < d := sub_pos.mpr (Q.lower_lt_upper i₀)
  have hside : ∀ i, Q.upper i - Q.lower i = d := fun i => hQ i i₀
  obtain ⟨j, hjlo, hjhi⟩ := exists_dyadic_reference
    (show 0 < 2 * (((n : ℝ) + 1) * d) by positivity)
  let P := ball (cubeCorner Q) (8 * (((n : ℝ) + 1) * d))
  have hP : MeasurableSet P := isOpen_ball.measurableSet
  have hq0 : 0 ≤ q := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hB (i : s) : BddAbove (range fun x => ‖K i x‖) := by
    refine ⟨C * ((2 : ℝ) ^ i.val) ^ n, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact bounded_of_polynomial_decay (by positivity) hq0 hC (hK i) x
  let u := fun i x => convolveKernel (K i) (f i) x
  let a := fun i x => lowScaleDifference Subtype.val j L (fun i => u i x)
    (fun i => u i (cubeCorner Q)) i
  let b := fun i x => middleScaleTerm Subtype.val j L (fun i => u i x) i
  let c := fun i x => highScaleTerm Subtype.val j L
    (fun i => convolveKernel (K i) (P.indicator (f i)) x) i
  let t := fun i x => highScaleTerm Subtype.val j L
    (fun i => convolveKernel (K i) (Pᶜ.indicator (f i)) x) i
  let w := lowScaleCenter Subtype.val j L (fun i => u i (cubeCorner Q))
  have hu (i : s) : Measurable (u i) :=
    (continuous_convolveKernel (hfi i) (hKd i).continuous (hB i)).measurable
  have ha (i : s) : Measurable (a i) := by
    dsimp only [a, lowScaleDifference]
    split_ifs
    · exact (hu i).sub measurable_const
    · exact measurable_const
  have hb (i : s) : Measurable (b i) := by
    dsimp only [b, middleScaleTerm]
    split_ifs
    · exact hu i
    · exact measurable_const
  have hc (i : s) : Measurable (c i) := by
    dsimp only [c, highScaleTerm]
    split_ifs
    · exact (continuous_convolveKernel ((hfi i).indicator hP) (hKd i).continuous (hB i)).measurable
    · exact measurable_const
  have ht (i : s) : Measurable (t i) := by
    dsimp only [t, highScaleTerm]
    split_ifs
    · exact (continuous_convolveKernel ((hfi i).indicator hP.compl) (hKd i).continuous (hB i)).measurable
    · exact measurable_const
  have hdecomp (x : Space n) (i : s) : u i x - w i = a i x + b i x + c i x + t i x := by
    exact scale_decomposition Subtype.val (j := j) hL (fun i => u i x)
      (fun i => u i (cubeCorner Q))
      (fun i => convolveKernel (K i) (P.indicator (f i)) x)
      (fun i => convolveKernel (K i) (Pᶜ.indicator (f i)) x)
      (fun i _ => convolveKernel_indicator_add_compl (hfi i) (hKd i).continuous (hB i) hP x) i
  refine ⟨vectorNorm w, ?_⟩
  intro z hz
  have havg := centered_vector_average_le_four volume (measurable_euclideanBox Q)
    u a b c t w ha hb hc ht (fun x hx => hdecomp x)
  apply havg.trans
  unfold convolutionEnvelope
  apply add_le_add
  · apply add_le_add
    · apply add_le_add
      · apply set_average_le_const volume (measurable_euclideanBox Q)
          (by rw [volume_euclideanBox]; exact volume_box_ne_zero Q)
          (by rw [volume_euclideanBox]; exact (Q.measure_coe_lt_top volume).ne)
        intro x hx
        have hh := ENNReal.ofReal_le_ofReal (low_cube_vector s Q hd hside
          (by linarith : (n : ℝ) < q) hC K f hKd hK' hB hfm hfi hL.le hjhi hx hz (hM z))
        convert hh using 1
        rw [← ENNReal.ofReal_toReal (hM z), ← ENNReal.ofReal_mul (scaleKernelConstant_nonneg hC)]
        congr 1
        unfold scaleKernelConstant
        simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
        ring
      · exact middle_cube_vector_average s Q hd hside u hu j L hp hz
    · apply localized_cube_vector_average Q hd hside c f hc hfm (z := z) (hz := hz)
      intro i
      dsimp only [c, highScaleTerm]
      split_ifs
      · exact h2 i _ ((hfi i).indicator hP) ((hf2 i).indicator hP)
      · change eLpNorm (0 : Space n → H) 2 volume ≤ _
        rw [eLpNorm_zero]
        exact bot_le
  · apply set_average_le_const volume (measurable_euclideanBox Q)
      (by rw [volume_euclideanBox]; exact volume_box_ne_zero Q)
      (by rw [volume_euclideanBox]; exact (Q.measure_coe_lt_top volume).ne)
    intro x hx
    have hh := ENNReal.ofReal_le_ofReal (high_cube_vector s Q hd hside hq hC K f hK hfm
      hjlo (L := L) hx hz (hM z))
    convert hh using 1
    rw [← ENNReal.ofReal_toReal (hM z), ← ENNReal.ofReal_mul (scaleKernelConstant_nonneg hC)]
    congr 1
    unfold scaleKernelConstant
    simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    ring

end OAI.Analysis.Fourier.SquareFunction
