import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanFourier
import OAI.RepresentationTheory.Weil.AdelicSplitting.ComplexNormalization
import OAI.RepresentationTheory.Weil.AdelicSplitting.RealNormalization
import OAI.RepresentationTheory.Weil.AdelicSplitting.RealDilationScale

/-! # Character Scaling Sq -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.CharacterScalingSq.LocalAnalysis

noncomputable section

/-! Fourier Plancherel on L¹ ∩ L² for every allowed real and complex
character, with the exact self-dual measure prescribed by AdelicSplitting. -/

open _root_.MeasureTheory
open scoped NNReal ENNReal

theorem positionFourier_rescaled_norm_sq
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    (N : ℕ) (ψ : AddChar k ℂ) (b : k) (hb : b ≠ 0) (μ : Measure k) [μ.IsAddHaarMeasure]
    (f : Local.FunctionsMetaplectic.Construction.Position k N → ℂ)
    (hF : (∫ x, ‖Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin N => μ)) f x‖ ^ 2
      ∂Measure.pi (fun _ : Fin N => μ)) = ∫ x, ‖f x‖ ^ 2 ∂Measure.pi (fun _ : Fin N => μ)) :
    let a := Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ) ^ N
    let ν := ENNReal.ofReal a • Measure.pi (fun _ : Fin N => μ)
    (∫ x, ‖Local.FunctionsMetaplectic.Construction.fourierIntegral (ψ.mulShift b) ν f x‖ ^ 2 ∂ν) = ∫ x, ‖f x‖ ^ 2 ∂ν := by
  let c : ℝ := DeterminantMeasure.LocalAnalysis.haarModulus k b
  let a := Real.sqrt c ^ N
  have hc : 0 < c := DeterminantMeasure.LocalAnalysis.haarModulus_pos k hb
  have ha : 0 < a := pow_pos (Real.sqrt_pos.mpr hc) _
  have htransform (x : Local.FunctionsMetaplectic.Construction.Position k N) :
      Local.FunctionsMetaplectic.Construction.fourierIntegral (ψ.mulShift b) (ENNReal.ofReal a • Measure.pi (fun _ : Fin N => μ)) f x =
        (a : ℂ) * Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin N => μ)) f (b • x) := by
    rw [Local.FunctionsMetaplectic.Construction.fourierIntegral, integral_smul_measure, ENNReal.toReal_ofReal ha.le, Complex.real_smul]
    congr 1
    exact CharacterScaling.LocalAnalysis.fourierIntegral_mulShift N ψ b _ f x
  change (∫ x, ‖Local.FunctionsMetaplectic.Construction.fourierIntegral (ψ.mulShift b)
    (ENNReal.ofReal a • Measure.pi (fun _ : Fin N => μ)) f x‖ ^ 2
    ∂ENNReal.ofReal a • Measure.pi (fun _ : Fin N => μ)) = _
  simp_rw [htransform, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, mul_pow]
  rw [integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal ha.le,
    integral_const_mul, CharacterScaling.LocalAnalysis.integral_scalar_position N b hb μ
      (fun x => ‖Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin N => μ)) f x‖ ^ 2), hF]
  have ha2 : a ^ 2 = c ^ N := by
    change (Real.sqrt c ^ N) ^ 2 = c ^ N
    rw [← pow_mul, Nat.mul_comm N 2, pow_mul, Real.sq_sqrt hc.le]
  change a * (a ^ 2 * ((c ^ N)⁻¹ * _)) = a * _
  rw [ha2, ← mul_assoc (c ^ N), mul_inv_cancel₀ (pow_ne_zero _ hc.ne'), one_mul]

theorem real_fourier_L2_normalized {N : ℕ} (ψ : AddChar ℝ ℂ)
    (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    {f : Local.FunctionsMetaplectic.Construction.Position ℝ N → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    (∫ x, ‖Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure ℝ N ψ) f x‖ ^ 2 ∂ Local.FunctionsMetaplectic.Construction.positionMeasure ℝ N ψ) =
      ∫ x, ‖f x‖ ^ 2 ∂ Local.FunctionsMetaplectic.Construction.positionMeasure ℝ N ψ := by
  obtain ⟨b, hb, rfl⟩ := RealCharacters.LocalAnalysis.continuous_nontrivial_unitary_real_character ψ hc hu hn
  have hchar : RealCharacters.LocalAnalysis.realCharacter b = (RealCharacters.LocalAnalysis.realCharacter 1).mulShift b := by
    ext x
    change (Real.fourierChar (b * x) : ℂ) = (Real.fourierChar (1 * (b * x)) : ℂ)
    rw [one_mul]
  have hmod : (DeterminantMeasure.LocalAnalysis.haarModulus ℝ b : ℝ) = |b| := by
    exact (congrArg (fun z : ℝ≥0 => (z : ℝ))
      (DeterminantMeasure.LocalAnalysis.haarModulus_unit ℝ (Units.mk0 b hb))).trans (RealDilationScale.LocalAnalysis.localModulus_real (Units.mk0 b hb))
  rw [RealNormalization.LocalAnalysis.positionMeasure_real N b hb, hchar]
  simpa only [hmod] using! positionFourier_rescaled_norm_sq N (RealCharacters.LocalAnalysis.realCharacter 1) b hb volume f
    (ArchimedeanFourier.LocalAnalysis.real_coordinate_fourier_L2 hf hf2)

theorem complex_fourier_L2_normalized {N : ℕ} (ψ : AddChar ℂ ℂ)
    (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    {f : Local.FunctionsMetaplectic.Construction.Position ℂ N → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    (∫ x, ‖Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure ℂ N ψ) f x‖ ^ 2 ∂ Local.FunctionsMetaplectic.Construction.positionMeasure ℂ N ψ) =
      ∫ x, ‖f x‖ ^ 2 ∂ Local.FunctionsMetaplectic.Construction.positionMeasure ℂ N ψ := by
  obtain ⟨b, hb, rfl⟩ := ComplexNormalization.LocalAnalysis.continuous_nontrivial_unitary_complex_character ψ hc hu hn
  rw [ComplexNormalization.LocalAnalysis.positionMeasure_complex N b hb]
  exact positionFourier_rescaled_norm_sq N ComplexFourier.LocalAnalysis.complexStandardCharacter b hb volume f
    (ArchimedeanFourier.LocalAnalysis.complex_coordinate_fourier_L2 hf hf2)

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.CharacterScalingSq.LocalAnalysis
