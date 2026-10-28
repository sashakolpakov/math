import OAI.RepresentationTheory.Weil.AdelicSplitting.ComplexNormalization
import OAI.RepresentationTheory.Weil.AdelicSplitting.RealNormalization

/-! # Scalar Plancherel -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ScalarPlancherel.LocalAnalysis

noncomputable section

/-! Scalar Plancherel, including arbitrary compact indicators, at both
archimedean models. This permits transport of the reference-set normalization. -/

open _root_.MeasureTheory
open scoped NNReal ENNReal FourierTransform ComplexConjugate

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]

theorem selfDualMeasure_mulShift (ψ : AddChar k ℂ)
    (hs : 0 < Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ) (b : k) (hb : b ≠ 0) :
    Local.FunctionsMetaplectic.Construction.selfDualMeasure k (ψ.mulShift b) =
      ENNReal.ofReal (Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ)) • Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ := by
  rw [Local.FunctionsMetaplectic.Construction.selfDualMeasure, Local.FunctionsMetaplectic.Construction.selfDualMeasure, CharacterScaling.LocalAnalysis.fourierHaarScaleSquared_mulShift _ _ hb,
    Real.sqrt_div hs.le, inv_div, smul_smul,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), div_eq_mul_inv]

omit [LocallyCompactSpace k] [BorelSpace k] [SecondCountableTopology k] in
theorem scalarFourier_mulShift (ψ : AddChar k ℂ) (b : k)
    (μ : Measure k) (f : k → ℂ) (x : k) :
    TensorFourier.LocalAnalysis.scalarFourier (ψ.mulShift b) μ f x = TensorFourier.LocalAnalysis.scalarFourier ψ μ f (b * x) := by
  unfold TensorFourier.LocalAnalysis.scalarFourier
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    change f y * ψ (b * -(x * y)) = f y * ψ (-((b * x) * y))
    congr 2
    ring

omit [LocallyCompactSpace k] [BorelSpace k] [SecondCountableTopology k] in
theorem scalarFourier_smul_measure (ψ : AddChar k ℂ) (a : ℝ) (ha : 0 ≤ a)
    (μ : Measure k) (f : k → ℂ) (x : k) :
    TensorFourier.LocalAnalysis.scalarFourier ψ (ENNReal.ofReal a • μ) f x = (a : ℂ) * TensorFourier.LocalAnalysis.scalarFourier ψ μ f x := by
  rw [TensorFourier.LocalAnalysis.scalarFourier, integral_smul_measure, ENNReal.toReal_ofReal ha, Complex.real_smul]
  rfl

theorem scalarFourier_rescaled_norm_sq (ψ : AddChar k ℂ) (b : k) (hb : b ≠ 0)
    (μ : Measure k) [μ.IsAddHaarMeasure] (f : k → ℂ)
    (hF : (∫ x, ‖TensorFourier.LocalAnalysis.scalarFourier ψ μ f x‖ ^ 2 ∂μ) = ∫ x, ‖f x‖ ^ 2 ∂μ) :
    (∫ x, ‖TensorFourier.LocalAnalysis.scalarFourier (ψ.mulShift b)
      (ENNReal.ofReal (Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ)) • μ) f x‖ ^ 2
      ∂(ENNReal.ofReal (Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ)) • μ)) =
    ∫ x, ‖f x‖ ^ 2 ∂(ENNReal.ofReal (Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ)) • μ) := by
  let c : ℝ := DeterminantMeasure.LocalAnalysis.haarModulus k b
  have hc : 0 < c := DeterminantMeasure.LocalAnalysis.haarModulus_pos k hb
  simp_rw [scalarFourier_smul_measure _ _ (Real.sqrt_nonneg _), scalarFourier_mulShift,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  rw [integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    integral_const_mul, CharacterScaling.LocalAnalysis.integral_scalar_field b hb μ (fun x => ‖TensorFourier.LocalAnalysis.scalarFourier ψ μ f x‖ ^ 2), hF]
  simp only [smul_eq_mul]
  change Real.sqrt c * ((Real.sqrt c ^ 2) * (c⁻¹ * _)) = Real.sqrt c * _
  rw [Real.sq_sqrt hc.le, ← mul_assoc c, mul_inv_cancel₀ hc.ne', one_mul]

theorem scalarFourier_real_standard (f : ℝ → ℂ) (x : ℝ) :
    TensorFourier.LocalAnalysis.scalarFourier (RealCharacters.LocalAnalysis.realCharacter 1) volume f x = 𝓕 f x := by
  rw [Real.fourier_eq]
  unfold TensorFourier.LocalAnalysis.scalarFourier
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    simp only [RealCharacters.LocalAnalysis.realCharacter, MonoidHom.compAddChar_apply, AddChar.mulShift_apply,
      one_mul, Function.comp_apply, Circle.smul_def, smul_eq_mul]
    change f y * (Real.fourierChar (-(x * y)) : ℂ) = (Real.fourierChar (-(x * y)) : ℂ) * f y
    exact mul_comm _ _

theorem scalarFourier_real_standard_norm_sq {f : ℝ → ℂ}
    (h₁ : Integrable f) (h₂ : MemLp f 2) :
    (∫ x, ‖TensorFourier.LocalAnalysis.scalarFourier (RealCharacters.LocalAnalysis.realCharacter 1) volume f x‖ ^ 2) = ∫ x, ‖f x‖ ^ 2 := by
  simp_rw [scalarFourier_real_standard]
  exact RealCharacters.LocalAnalysis.real_integral_fourier_norm_sq h₁ h₂

theorem scalarFourier_complex_standard_norm_sq {f : ℂ → ℂ}
    (h₁ : Integrable f) (h₂ : MemLp f 2) :
    (∫ x, ‖TensorFourier.LocalAnalysis.scalarFourier ComplexFourier.LocalAnalysis.complexStandardCharacter volume f x‖ ^ 2) = ∫ x, ‖f x‖ ^ 2 := by
  simp_rw [ComplexFourier.LocalAnalysis.scalarFourier_complex_standard]
  have hconj : (∫ x : ℂ, ‖𝓕 f (conj x)‖ ^ 2) = ∫ x : ℂ, ‖𝓕 f x‖ ^ 2 := by
    simpa using! Complex.conjLIE.measurePreserving.integral_comp
      Complex.conjLIE.toHomeomorph.measurableEmbedding (fun x => ‖𝓕 f x‖ ^ 2)
  rw [hconj]
  exact RealCharacters.LocalAnalysis.real_integral_fourier_norm_sq h₁ h₂

theorem real_scalar_indicator_plancherel
    (ψ : AddChar ℝ ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    {S : Set ℝ} (hS : IsCompact S) :
    (∫ x, ‖TensorFourier.LocalAnalysis.scalarFourier ψ (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ) (S.indicator (fun _ => (1 : ℂ))) x‖ ^ 2
      ∂ Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ) = (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ).real S := by
  obtain ⟨b, hb, rfl⟩ := RealCharacters.LocalAnalysis.continuous_nontrivial_unitary_real_character ψ hc hu hn
  have hchar : RealCharacters.LocalAnalysis.realCharacter b = (RealCharacters.LocalAnalysis.realCharacter 1).mulShift b := by
    ext x
    change (Real.fourierChar (b * x) : ℂ) = (Real.fourierChar (1 * (b * x)) : ℂ)
    rw [one_mul]
  rw [hchar, selfDualMeasure_mulShift _ RealCharacters.LocalAnalysis.fourierHaarScaleSquared_real_standard_pos b hb,
    RealCharacters.LocalAnalysis.selfDualMeasure_real_standard]
  have hf (p : ℝ≥0∞) : MemLp (S.indicator (fun _ => (1 : ℂ))) p :=
    memLp_indicator_const p hS.measurableSet 1 (Or.inr hS.measure_ne_top)
  rw [scalarFourier_rescaled_norm_sq _ _ hb _ _
    (scalarFourier_real_standard_norm_sq (memLp_one_iff_integrable.mp (hf 1)) (hf 2))]
  have he : (fun x => ‖S.indicator (fun _ => (1 : ℂ)) x‖ ^ 2) = S.indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ S <;> simp [hx]
  rw [he]
  exact integral_indicator_one hS.measurableSet

theorem complex_scalar_indicator_plancherel
    (ψ : AddChar ℂ ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    {S : Set ℂ} (hS : IsCompact S) :
    (∫ x, ‖TensorFourier.LocalAnalysis.scalarFourier ψ (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ) (S.indicator (fun _ => (1 : ℂ))) x‖ ^ 2
      ∂ Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ) = (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ).real S := by
  obtain ⟨b, hb, rfl⟩ := ComplexNormalization.LocalAnalysis.continuous_nontrivial_unitary_complex_character ψ hc hu hn
  have hs : 0 < Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared ℂ ComplexFourier.LocalAnalysis.complexStandardCharacter := by
    rw [ComplexFourier.LocalAnalysis.fourierHaarScaleSquared_complex_standard]
    exact sq_pos_of_pos ComplexFourier.LocalAnalysis.complexReferenceHaarFactor_pos
  rw [ComplexNormalization.LocalAnalysis.complexCharacter, selfDualMeasure_mulShift _ hs b hb, ComplexFourier.LocalAnalysis.selfDualMeasure_complex_standard]
  have hf (p : ℝ≥0∞) : MemLp (S.indicator (fun _ => (1 : ℂ))) p :=
    memLp_indicator_const p hS.measurableSet 1 (Or.inr hS.measure_ne_top)
  rw [scalarFourier_rescaled_norm_sq _ _ hb _ _
    (scalarFourier_complex_standard_norm_sq (memLp_one_iff_integrable.mp (hf 1)) (hf 2))]
  have he : (fun x => ‖S.indicator (fun _ => (1 : ℂ)) x‖ ^ 2) = S.indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ S <;> simp [hx]
  rw [he]
  exact integral_indicator_one hS.measurableSet

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ScalarPlancherel.LocalAnalysis
