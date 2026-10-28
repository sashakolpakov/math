import OAI.Analysis.Fourier.SquareFunction.CommonInput
import OAI.Analysis.Fourier.SquareFunction.CombiningScales

open OAI.Analysis.Fourier.Wave

/-! A common-input square-function estimate from an aggregate L² bound.
This is the sharp-function part of the Littlewood–Paley upper estimate. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set Metric
open scoped ENNReal

theorem vectorNorm_unit_nonneg {r : ℝ} (hr : 0 ≤ r) :
    vectorNorm (fun _ : Unit => r) = r := by
  simp only [vectorNorm_eq_sqrt, Finset.univ_unique, Finset.sum_singleton]
  rw [Real.norm_eq_abs, sq_abs, Real.sqrt_sq hr]

theorem localized_common_vector_average {n : ℕ} {I H : Type*} [Fintype I]
    [NormedAddCommGroup H] [MeasurableSpace H] [BorelSpace H]
    (Q : BoxIntegral.Box (Fin n)) {d : ℝ} (hd : 0 < d)
    (hside : ∀ i, Q.upper i - Q.lower i = d)
    (u : I → Space n → H) (f : Space n → ℂ)
    (hu : ∀ i, Measurable (u i)) (hf : Measurable f) {B : ℝ≥0∞}
    (h2 : eLpNorm (fun x => vectorNorm (fun i => u i x)) 2 volume ≤ B * eLpNorm
      ((ball (cubeCorner Q) (8 * (((n : ℝ) + 1) * d))).indicator f) 2 volume)
    {z : Space n} (hz : z ∈ euclideanBox Q) :
    (∫⁻ x in euclideanBox Q, ENNReal.ofReal (vectorNorm (fun i => u i x))) /
      volume (euclideanBox Q) ≤ B * (cubeBallRatio n * ballMaximal volume
        (fun x => ‖f x‖ₑ ^ (2 : ℝ)) z) ^ (1 / 2 : ℝ) := by
  have hh := localized_cube_vector_average Q hd hside
    (fun _ : Unit => fun x => vectorNorm (fun i => u i x)) (fun _ : Unit => f)
    (fun _ => measurable_vectorNorm u hu) (fun _ => hf) (fun _ => h2) hz
  simpa only [vectorNorm_unit_nonneg (vectorNorm_nonneg _),
    Finset.univ_unique, Finset.sum_singleton] using hh

noncomputable def commonInputEnvelope {n : ℕ} (f : Space n → ℂ)
    (q C : ℝ) (B : ℝ≥0∞) (z : Space n) : ℝ≥0∞ :=
  ENNReal.ofReal (scaleKernelConstant n q q C 0) * ballMaximal volume (fun y => ‖f y‖ₑ) z +
    B * (cubeBallRatio n * ballMaximal volume (fun y => ‖f y‖ₑ ^ (2 : ℝ)) z) ^ (1 / 2 : ℝ) +
    ENNReal.ofReal (scaleKernelConstant n q (q - 1) C 1) * ballMaximal volume (fun y => ‖f y‖ₑ) z

theorem common_input_cube_oscillation {n : ℕ} [NeZero n] {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (s : Finset ℤ) (K : s → Space n → H) (f : Space n → ℂ)
    {q C : ℝ} (hq : (n : ℝ) + 1 < q) (hC : 0 ≤ C)
    (hKd : ∀ i, Differentiable ℝ (K i))
    (hK : ∀ i u, ‖K i u‖ ≤ C * ((2 : ℝ) ^ i.val) ^ n *
      ((2 : ℝ) ^ i.val * ‖u‖ + 1) ^ (-q))
    (hK' : ∀ i u, ‖fderiv ℝ (K i) u‖ ≤ C * (((2 : ℝ) ^ i.val) ^ n * (2 : ℝ) ^ i.val) *
      ((2 : ℝ) ^ i.val * ‖u‖ + 1) ^ (-q))
    (hfm : Measurable f) (hfi : Integrable f) (hf2 : MemLp f 2 volume) {B : ℝ≥0∞}
    (h2 : ∀ (g : Space n → ℂ), Integrable g → MemLp g 2 volume →
      eLpNorm (fun x => vectorNorm (fun i => convolveKernel (K i) g x)) 2 volume ≤ B * eLpNorm g 2 volume)
    (hM : ∀ z, ballMaximal volume (fun y => ‖f y‖ₑ) z ≠ ∞)
    (Q : BoxIntegral.Box (Fin n)) (hQ : IsCubeBox Q) :
    ∃ c : ℝ, ∀ z ∈ euclideanBox Q,
      (∫⁻ x in euclideanBox Q, ‖vectorNorm (fun i => convolveKernel (K i) f x) - c‖ₑ) /
        volume (euclideanBox Q) ≤ commonInputEnvelope f q C B z := by
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
  let u := fun i x => convolveKernel (K i) f x
  let a := fun i x => lowScaleDifference Subtype.val j 0 (fun i => u i x)
    (fun i => u i (cubeCorner Q)) i
  let c := fun i x => highScaleTerm Subtype.val j 1
    (fun i => convolveKernel (K i) (P.indicator f) x) i
  let t := fun i x => highScaleTerm Subtype.val j 1
    (fun i => convolveKernel (K i) (Pᶜ.indicator f) x) i
  let w := lowScaleCenter Subtype.val j 0 (fun i => u i (cubeCorner Q))
  have hu (i : s) : Measurable (u i) :=
    (continuous_convolveKernel hfi (hKd i).continuous (hB i)).measurable
  have ha (i : s) : Measurable (a i) := by
    dsimp only [a, lowScaleDifference]
    split_ifs
    · exact (hu i).sub measurable_const
    · exact measurable_const
  have hc (i : s) : Measurable (c i) := by
    dsimp only [c, highScaleTerm]
    split_ifs
    · exact (continuous_convolveKernel (hfi.indicator hP) (hKd i).continuous (hB i)).measurable
    · exact measurable_const
  have ht (i : s) : Measurable (t i) := by
    dsimp only [t, highScaleTerm]
    split_ifs
    · exact (continuous_convolveKernel (hfi.indicator hP.compl) (hKd i).continuous (hB i)).measurable
    · exact measurable_const
  have hdecomp (x : Space n) (i : s) : u i x - w i = a i x + 0 + c i x + t i x := by
    by_cases hi : i.val ≤ j
    · have hi' : ¬j + 1 ≤ i.val := by omega
      simp only [w, a, c, t, lowScaleCenter, lowScaleDifference, highScaleTerm,
        sub_zero, hi, hi', ite_true, ite_false, add_zero]
    · have hi' : j + 1 ≤ i.val := by omega
      simpa only [u, w, a, c, t, lowScaleCenter, lowScaleDifference, highScaleTerm,
        sub_zero, hi, hi', ite_false, ite_true, add_zero, zero_add] using
        convolveKernel_indicator_add_compl hfi (hKd i).continuous (hB i) hP x
  refine ⟨vectorNorm w, ?_⟩
  intro z hz
  have havg := centered_vector_average_le_four volume (measurable_euclideanBox Q)
    u a (fun _ _ => (0 : H)) c t w ha (fun _ => measurable_const) hc ht (fun x _ => hdecomp x)
  have hzero : (∫⁻ x in euclideanBox Q,
      ENNReal.ofReal (vectorNorm (fun _ : s => (0 : H)))) / volume (euclideanBox Q) = 0 := by
    simp [vectorNorm_eq_sqrt]
  rw [hzero, add_zero] at havg
  apply havg.trans
  unfold commonInputEnvelope
  apply add_le_add
  · apply add_le_add
    · apply set_average_le_const volume (measurable_euclideanBox Q)
        (by rw [volume_euclideanBox]; exact volume_box_ne_zero Q)
        (by rw [volume_euclideanBox]; exact (Q.measure_coe_lt_top volume).ne)
      intro x hx
      have hh := ENNReal.ofReal_le_ofReal (low_cube_common_input s Q hd hside
        (by linarith : (n : ℝ) < q) hC K f hKd hK' hB hfm hfi (L := 0)
        (by norm_num) hjhi hx hz (hM z))
      simpa only [ENNReal.ofReal_mul (scaleKernelConstant_nonneg hC), ENNReal.ofReal_toReal (hM z)] using hh
    · apply localized_common_vector_average Q hd hside c f hc hfm (z := z) (hz := hz)
      apply le_trans _ (h2 _ (hfi.indicator hP) (hf2.indicator hP))
      apply eLpNorm_mono (measurable_vectorNorm c hc).aestronglyMeasurable
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (vectorNorm_nonneg _),
        Real.norm_eq_abs, abs_of_nonneg (vectorNorm_nonneg _)]
      apply vectorNorm_mono
      intro i
      dsimp only [c, highScaleTerm]
      split_ifs
      · exact le_rfl
      · simpa only [norm_zero] using norm_nonneg (convolveKernel (K i) (P.indicator f) x)
  · apply set_average_le_const volume (measurable_euclideanBox Q)
      (by rw [volume_euclideanBox]; exact volume_box_ne_zero Q)
      (by rw [volume_euclideanBox]; exact (Q.measure_coe_lt_top volume).ne)
    intro x hx
    have hh := ENNReal.ofReal_le_ofReal (high_cube_common_input s Q hd hside hq hC K f hK hfm
      hjlo (L := 1) hx hz (hM z))
    simpa only [ENNReal.ofReal_mul (scaleKernelConstant_nonneg hC), ENNReal.ofReal_toReal (hM z)] using hh

end OAI.Analysis.Fourier.SquareFunction
