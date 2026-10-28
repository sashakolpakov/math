import OAI.RepresentationTheory.Weil.AdelicSplitting.ComplexFourier
import OAI.RepresentationTheory.Weil.AdelicSplitting.CharacterScaling
import OAI.RepresentationTheory.Weil.AdelicSplitting.FourierIntertwiner

/-! # Complex Normalization -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ComplexNormalization.LocalAnalysis

noncomputable section

/-! The exact raw complex Fourier oscillator for every continuous
nontrivial unitary character allowed by AdelicSplitting. -/

open _root_.MeasureTheory
open scoped NNReal ENNReal

def complexCharacter (b : ℂ) : AddChar ℂ ℂ := ComplexFourier.LocalAnalysis.complexStandardCharacter.mulShift b

theorem continuous_nontrivial_unitary_complex_character
    (ψ : AddChar ℂ ℂ) (hc : Continuous ψ) (hu : ∀ z, ‖ψ z‖ = 1) (hn : ∃ z, ψ z ≠ 1) :
    ∃ b : ℂ, b ≠ 0 ∧ ψ = complexCharacter b := by
  obtain ⟨b, hb⟩ := ComplexFourier.LocalAnalysis.complex_character_coefficient ψ hc hu
  have hbn : b ≠ 0 := by
    intro hzero
    obtain ⟨z, hz⟩ := hn
    apply hz
    rw [hb, hzero, zero_mul, ComplexFourier.LocalAnalysis.complexStandardCharacter.map_zero_eq_one]
  exact ⟨b, hbn, DFunLike.ext _ _ hb⟩

theorem fourierHaarScaleSquared_complex (b : ℂ) (hb : b ≠ 0) :
    Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared ℂ (complexCharacter b) =
      (ComplexFourier.LocalAnalysis.complexReferenceHaarFactor : ℝ) ^ 2 / (DeterminantMeasure.LocalAnalysis.haarModulus ℂ b : ℝ) := by
  rw [complexCharacter, CharacterScaling.LocalAnalysis.fourierHaarScaleSquared_mulShift _ _ hb,
    ComplexFourier.LocalAnalysis.fourierHaarScaleSquared_complex_standard]

theorem fourierHaarScaleSquared_complex_pos (b : ℂ) (hb : b ≠ 0) :
    0 < Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared ℂ (complexCharacter b) := by
  rw [fourierHaarScaleSquared_complex b hb]
  exact div_pos (sq_pos_of_pos ComplexFourier.LocalAnalysis.complexReferenceHaarFactor_pos) (DeterminantMeasure.LocalAnalysis.haarModulus_pos ℂ hb)

theorem selfDualMeasure_complex (b : ℂ) (hb : b ≠ 0) :
    Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ (complexCharacter b) =
      ENNReal.ofReal (Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus ℂ b : ℝ)) • volume := by
  have hr : (ComplexFourier.LocalAnalysis.complexReferenceHaarFactor : ℝ) ≠ 0 :=
    (show (0 : ℝ) < ComplexFourier.LocalAnalysis.complexReferenceHaarFactor from ComplexFourier.LocalAnalysis.complexReferenceHaarFactor_pos).ne'
  have hs : Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus ℂ b : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (DeterminantMeasure.LocalAnalysis.haarModulus_pos ℂ hb)).ne'
  have hscale : (Real.sqrt ((ComplexFourier.LocalAnalysis.complexReferenceHaarFactor : ℝ) ^ 2 /
      (DeterminantMeasure.LocalAnalysis.haarModulus ℂ b : ℝ)))⁻¹ * (ComplexFourier.LocalAnalysis.complexReferenceHaarFactor : ℝ) =
      Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus ℂ b : ℝ) := by
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq ComplexFourier.LocalAnalysis.complexReferenceHaarFactor.coe_nonneg]
    field_simp
  rw [Local.FunctionsMetaplectic.Construction.selfDualMeasure, fourierHaarScaleSquared_complex b hb,
    Measure.isAddLeftInvariant_eq_smul_of_regular (Measure.addHaar : Measure ℂ) volume]
  change ENNReal.ofReal (Real.sqrt ((ComplexFourier.LocalAnalysis.complexReferenceHaarFactor : ℝ) ^ 2 /
      (DeterminantMeasure.LocalAnalysis.haarModulus ℂ b : ℝ)))⁻¹ • (ComplexFourier.LocalAnalysis.complexReferenceHaarFactor • volume) = _
  rw [ENNReal.smul_def, smul_smul]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity), hscale]

theorem positionMeasure_complex (n : ℕ) (b : ℂ) (hb : b ≠ 0) :
    Local.FunctionsMetaplectic.Construction.positionMeasure ℂ n (complexCharacter b) =
      ENNReal.ofReal (Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus ℂ b : ℝ) ^ n) • volume := by
  unfold Local.FunctionsMetaplectic.Construction.positionMeasure
  simp_rw [selfDualMeasure_complex b hb]
  let : (ENNReal.ofReal (Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus ℂ b : ℝ)) • (volume : Measure ℂ)).IsAddHaarMeasure := by
    apply Measure.IsAddHaarMeasure.smul
    · exact (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (DeterminantMeasure.LocalAnalysis.haarModulus_pos ℂ hb))).ne'
    · exact ENNReal.ofReal_ne_top
  refine Measure.pi_eq (μ := fun _ : Fin n =>
    ENNReal.ofReal (Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus ℂ b : ℝ)) • (volume : Measure ℂ)) fun s _ => ?_
  rw [Measure.smul_apply, volume_pi_pi]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (Real.sqrt_nonneg _)]

theorem complex_fourier_square_volume (n : ℕ) (b : ℂ) (hb : b ≠ 0)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) (x : Local.FunctionsMetaplectic.Construction.Position ℂ n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral (complexCharacter b) volume
      (Local.FunctionsMetaplectic.Construction.fourierIntegral (complexCharacter b) volume f.val) x =
      (((DeterminantMeasure.LocalAnalysis.haarModulus ℂ b : ℝ) ^ n)⁻¹ : ℝ) • f.val (-x) := by
  have hf : Local.FunctionsMetaplectic.Construction.fourierIntegral (complexCharacter b) volume f.val =
      fun y => Local.FunctionsMetaplectic.Construction.fourierIntegral ComplexFourier.LocalAnalysis.complexStandardCharacter volume f.val (b • y) :=
    funext (CharacterScaling.LocalAnalysis.fourierIntegral_mulShift n ComplexFourier.LocalAnalysis.complexStandardCharacter b volume f.val)
  rw [hf]
  change Local.FunctionsMetaplectic.Construction.fourierIntegral (ComplexFourier.LocalAnalysis.complexStandardCharacter.mulShift b) (Measure.pi (fun _ : Fin n => volume))
    (fun y => Local.FunctionsMetaplectic.Construction.fourierIntegral ComplexFourier.LocalAnalysis.complexStandardCharacter volume f.val (b • y)) x = _
  rw [CharacterScaling.LocalAnalysis.fourierIntegral_mulShift_scaled_input _ _ _ hb]
  congr 1
  exact ComplexFourier.LocalAnalysis.complex_fourier_inversion_standard n f x

theorem fourierIntegral_complex_normalized (n : ℕ) (b : ℂ) (hb : b ≠ 0)
    (f : Local.FunctionsMetaplectic.Construction.Position ℂ n → ℂ) (x : Local.FunctionsMetaplectic.Construction.Position ℂ n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral (complexCharacter b) (Local.FunctionsMetaplectic.Construction.positionMeasure ℂ n (complexCharacter b)) f x =
      (Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus ℂ b : ℝ) ^ n : ℝ) • Local.FunctionsMetaplectic.Construction.fourierIntegral (complexCharacter b) volume f x := by
  rw [positionMeasure_complex n b hb, Local.FunctionsMetaplectic.Construction.fourierIntegral, integral_smul_measure]
  rw [ENNReal.toReal_ofReal (by positivity)]
  rfl

theorem complex_fourier_inversion (n : ℕ) (b : ℂ) (hb : b ≠ 0)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) (x : Local.FunctionsMetaplectic.Construction.Position ℂ n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral (complexCharacter b) (Local.FunctionsMetaplectic.Construction.positionMeasure ℂ n (complexCharacter b))
      (Local.FunctionsMetaplectic.Construction.fourierIntegral (complexCharacter b) (Local.FunctionsMetaplectic.Construction.positionMeasure ℂ n (complexCharacter b)) f.val) x =
        f.val (-x) := by
  let c : ℝ := DeterminantMeasure.LocalAnalysis.haarModulus ℂ b
  have hc : 0 < c := DeterminantMeasure.LocalAnalysis.haarModulus_pos ℂ hb
  have hf : Local.FunctionsMetaplectic.Construction.fourierIntegral (complexCharacter b) (Local.FunctionsMetaplectic.Construction.positionMeasure ℂ n (complexCharacter b)) f.val =
      (Real.sqrt c ^ n : ℂ) • Local.FunctionsMetaplectic.Construction.fourierIntegral (complexCharacter b) volume f.val := by
    funext y
    rw [fourierIntegral_complex_normalized n b hb]
    simp only [c, Complex.real_smul, Pi.smul_apply, smul_eq_mul, Complex.ofReal_pow]
  rw [fourierIntegral_complex_normalized n b hb, hf, Local.FunctionsMetaplectic.Construction.fourierIntegral_smul,
    Pi.smul_apply, complex_fourier_square_volume n b hb]
  simp only [Complex.real_smul, smul_eq_mul]
  have hcoef : Real.sqrt c ^ n * Real.sqrt c ^ n * (c ^ n)⁻¹ = 1 := by
    rw [← mul_pow, Real.mul_self_sqrt hc.le, mul_inv_cancel₀ (pow_ne_zero _ hc.ne')]
  have hcoefC : (Real.sqrt c ^ n : ℂ) * (Real.sqrt c ^ n : ℂ) * (((c ^ n)⁻¹ : ℝ) : ℂ) = 1 := by
    exact_mod_cast hcoef
  calc
    _ = ((Real.sqrt c ^ n : ℂ) * (Real.sqrt c ^ n : ℂ) * (((c ^ n)⁻¹ : ℝ) : ℂ)) * f.val (-x) := by
      dsimp only [c]
      push_cast
      ring
    _ = _ := by rw [hcoefC, one_mul]

theorem complex_fourier_mem (n : ℕ) (b : ℂ) (hb : b ≠ 0) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral (complexCharacter b) (Local.FunctionsMetaplectic.Construction.positionMeasure ℂ n (complexCharacter b)) f.val ∈
      Local.FunctionsMetaplectic.Construction.schwartzBruhat ℂ n := by
  obtain ⟨φ, hφ⟩ := ArchimedeanCharacters.LocalAnalysis.schwartzBruhat_archimedean_iff.mp (ComplexFourier.LocalAnalysis.complex_fourier_mem_standard n f)
  let e := (CharacterScaling.LocalAnalysis.scalarPositionEquiv n b hb).restrictScalars ℝ
  let χ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e φ
  refine ArchimedeanCharacters.LocalAnalysis.schwartzBruhat_archimedean_iff.mpr
    ⟨(Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus ℂ b : ℝ) ^ n : ℂ) • χ, ?_⟩
  funext x
  rw [fourierIntegral_complex_normalized n b hb, complexCharacter, CharacterScaling.LocalAnalysis.fourierIntegral_mulShift, hφ]
  change (Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus ℂ b : ℝ) ^ n : ℝ) • φ (b • x) =
    (Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus ℂ b : ℝ) ^ n : ℂ) * φ (b • x)
  simp only [Complex.real_smul, Complex.ofReal_pow]

theorem complex_fourier_analysis (n : ℕ)
    (ψ : AddChar ℂ ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1) :
    0 < Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared ℂ ψ ∧
    (∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℂ n,
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ) f.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) ∧
    ∀ (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) x,
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ)
        (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ) f.val) x = f.val (-x) := by
  obtain ⟨b, hbn, rfl⟩ := continuous_nontrivial_unitary_complex_character ψ hc hu hn
  exact ⟨fourierHaarScaleSquared_complex_pos b hbn, complex_fourier_mem n b hbn,
    complex_fourier_inversion n b hbn⟩

def complexRawFourierOscillator (n : ℕ)
    (ψ : AddChar ℂ ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1) :
    Local.FunctionsMetaplectic.Construction.Oscillator ℂ n ψ := by
  have h := complex_fourier_analysis n ψ hc hu hn
  let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ).IsAddHaarMeasure :=
    FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℂ ψ h.1
  let : (Local.FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ).IsAddHaarMeasure := by unfold Local.FunctionsMetaplectic.Construction.positionMeasure; infer_instance
  exact FourierIntertwiner.LocalAnalysis.fourierOscillator ψ hu hc (Local.FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ) h.2.1 h.2.2

theorem complexRawFourierOscillator_apply (n : ℕ)
    (ψ : AddChar ℂ ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) (x : Local.FunctionsMetaplectic.Construction.Position ℂ n) :
    ((complexRawFourierOscillator n ψ hc hu hn).val.2 f).val x =
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ) f.val x := rfl

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ComplexNormalization.LocalAnalysis
