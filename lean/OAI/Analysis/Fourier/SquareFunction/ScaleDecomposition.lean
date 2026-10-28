import OAI.Analysis.Fourier.SquareFunction.LocalizedL2

/-! The actual low/middle/high vector decomposition used for the cube
oscillation argument, and its integration with no loss in the vector length. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set
open scoped ENNReal

theorem vector_oscillation_le_four {I H : Type*} [Fintype I] [SeminormedAddCommGroup H]
    (u w a b c d : I → H) (he : ∀ i, u i - w i = a i + b i + c i + d i) :
    |vectorNorm u - vectorNorm w| ≤
      vectorNorm a + vectorNorm b + vectorNorm c + vectorNorm d := by
  apply (abs_vectorNorm_sub_le u w).trans
  simpa only [funext he] using vectorNorm_four_add_le a b c d

theorem set_average_le_const {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {Q : Set X} (hQ : MeasurableSet Q)
    (hQ0 : μ Q ≠ 0) (hQtop : μ Q ≠ ∞) {f : X → ℝ≥0∞} {C : ℝ≥0∞}
    (hf : ∀ x ∈ Q, f x ≤ C) : (∫⁻ x in Q, f x ∂μ) / μ Q ≤ C := by
  calc
    _ ≤ (∫⁻ _x in Q, C ∂μ) / μ Q := ENNReal.div_le_div_right
      (lintegral_mono_ae (by filter_upwards [ae_restrict_mem hQ] with x hx using hf x hx)) _
    _ = _ := by rw [setLIntegral_const, ENNReal.mul_div_cancel_right hQ0 hQtop]

theorem centered_vector_average_le_four {X I H : Type*} [MeasurableSpace X] [Fintype I]
    [NormedAddCommGroup H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure X) {Q : Set X} (hQ : MeasurableSet Q)
    (u a b c d : I → X → H) (w : I → H)
    (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i))
    (hc : ∀ i, Measurable (c i)) (_ : ∀ i, Measurable (d i))
    (he : ∀ x ∈ Q, ∀ i, u i x - w i = a i x + b i x + c i x + d i x) :
    (∫⁻ x in Q, ‖vectorNorm (fun i => u i x) - vectorNorm w‖ₑ ∂μ) / μ Q ≤
      (∫⁻ x in Q, ENNReal.ofReal (vectorNorm (fun i => a i x)) ∂μ) / μ Q +
      (∫⁻ x in Q, ENNReal.ofReal (vectorNorm (fun i => b i x)) ∂μ) / μ Q +
      (∫⁻ x in Q, ENNReal.ofReal (vectorNorm (fun i => c i x)) ∂μ) / μ Q +
      (∫⁻ x in Q, ENNReal.ofReal (vectorNorm (fun i => d i x)) ∂μ) / μ Q := by
  have hp (x : X) (hx : x ∈ Q) : ‖vectorNorm (fun i => u i x) - vectorNorm w‖ₑ ≤
      ENNReal.ofReal (vectorNorm (fun i => a i x)) +
      ENNReal.ofReal (vectorNorm (fun i => b i x)) +
      ENNReal.ofReal (vectorNorm (fun i => c i x)) +
      ENNReal.ofReal (vectorNorm (fun i => d i x)) := by
    have h := ENNReal.ofReal_le_ofReal (vector_oscillation_le_four
      (fun i => u i x) w (fun i => a i x) (fun i => b i x)
      (fun i => c i x) (fun i => d i x) (he x hx))
    simpa only [← Real.norm_eq_abs, ofReal_norm,
      ENNReal.ofReal_add (add_nonneg (add_nonneg (vectorNorm_nonneg _)
        (vectorNorm_nonneg _)) (vectorNorm_nonneg _)) (vectorNorm_nonneg _),
      ENNReal.ofReal_add (add_nonneg (vectorNorm_nonneg _) (vectorNorm_nonneg _)) (vectorNorm_nonneg _),
      ENNReal.ofReal_add (vectorNorm_nonneg _) (vectorNorm_nonneg _)] using h
  have h := ENNReal.div_le_div_right
    (lintegral_mono_ae (μ := μ.restrict Q)
      (by filter_upwards [ae_restrict_mem hQ] with x hx using hp x hx)) (μ Q)
  have hma := (measurable_vectorNorm a ha).ennreal_ofReal
  have hmb := (measurable_vectorNorm b hb).ennreal_ofReal
  have hmc := (measurable_vectorNorm c hc).ennreal_ofReal
  have hmab : Measurable (fun x => ENNReal.ofReal (vectorNorm (fun i => a i x)) +
      ENNReal.ofReal (vectorNorm (fun i => b i x))) := hma.add hmb
  have hmabc : Measurable (fun x => ENNReal.ofReal (vectorNorm (fun i => a i x)) +
      ENNReal.ofReal (vectorNorm (fun i => b i x)) +
      ENNReal.ofReal (vectorNorm (fun i => c i x))) := hmab.add hmc
  rw [lintegral_add_left hmabc,
    lintegral_add_left hmab, lintegral_add_left hma,
    ENNReal.add_div, ENNReal.add_div, ENNReal.add_div] at h
  exact h

noncomputable def lowScaleCenter {I H : Type*} [Zero H]
    (k : I → ℤ) (j L : ℤ) (u : I → H) : I → H :=
  fun i => if k i ≤ j - L then u i else 0

noncomputable def lowScaleDifference {I H : Type*} [Sub H] [Zero H]
    (k : I → ℤ) (j L : ℤ) (u v : I → H) : I → H :=
  fun i => if k i ≤ j - L then u i - v i else 0

noncomputable def middleScaleTerm {I H : Type*} [Zero H]
    (k : I → ℤ) (j L : ℤ) (u : I → H) : I → H :=
  fun i => if j - L < k i ∧ k i < j + L then u i else 0

noncomputable def highScaleTerm {I H : Type*} [Zero H]
    (k : I → ℤ) (j L : ℤ) (u : I → H) : I → H :=
  fun i => if j + L ≤ k i then u i else 0

theorem scale_decomposition {I H : Type*} [AddCommGroup H]
    (k : I → ℤ) {j L : ℤ} (hL : 0 < L) (u v a b : I → H)
    (he : ∀ i, j + L ≤ k i → u i = a i + b i) (i : I) :
    u i - lowScaleCenter k j L v i =
      lowScaleDifference k j L u v i + middleScaleTerm k j L u i +
      highScaleTerm k j L a i + highScaleTerm k j L b i := by
  dsimp only [lowScaleCenter, lowScaleDifference, middleScaleTerm, highScaleTerm]
  by_cases hlo : k i ≤ j - L
  · have hmid : ¬ (j - L < k i ∧ k i < j + L) := by omega
    have hhi : ¬ j + L ≤ k i := by omega
    simp [hlo, hmid, hhi]
  · by_cases hhi : j + L ≤ k i
    · have hmid : ¬ (j - L < k i ∧ k i < j + L) := by omega
      simp [hlo, hmid, hhi, he i hhi]
    · have hmid : j - L < k i ∧ k i < j + L := by omega
      simp [hlo, hmid, hhi]

end OAI.Analysis.Fourier.SquareFunction
