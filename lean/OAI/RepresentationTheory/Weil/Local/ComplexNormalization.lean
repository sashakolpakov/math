import OAI.RepresentationTheory.Weil.Local.ComplexStandardNormalization
import OAI.RepresentationTheory.Weil.Local.CharacterScaling

/-! # Complex Normalization -/

namespace OAI.RepresentationTheory.Weil.Local.ComplexNormalization.Construction

noncomputable section

/-! The exact raw complex Fourier oscillator for every continuous
nontrivial unitary character allowed by LocalWeil. -/

open _root_.MeasureTheory
open scoped NNReal ENNReal

def complexCharacter (b : ℂ) : AddChar ℂ ℂ := ArchimedeanTestSpace.Construction.complexStandardCharacter.mulShift b

theorem continuous_nontrivial_unitary_complex_character
    (ψ : AddChar ℂ ℂ) (hc : Continuous ψ) (hu : ∀ z, ‖ψ z‖ = 1) (hn : ∃ z, ψ z ≠ 1) :
    ∃ b : ℂ, b ≠ 0 ∧ ψ = complexCharacter b := by
  obtain ⟨b, hb⟩ := ArchimedeanTestSpace.Construction.complex_character_coefficient ψ hc hu
  have hbn : b ≠ 0 := by
    intro hzero
    obtain ⟨z, hz⟩ := hn
    apply hz
    rw [hb, hzero, zero_mul, ArchimedeanTestSpace.Construction.complexStandardCharacter.map_zero_eq_one]
  exact ⟨b, hbn, DFunLike.ext _ _ hb⟩

theorem fourierHaarScaleSquared_complex (b : ℂ) (hb : b ≠ 0) :
    FunctionsMetaplectic.Construction.fourierHaarScaleSquared ℂ (complexCharacter b) =
      (ArchimedeanTestSpace.Construction.complexReferenceHaarFactor : ℝ) ^ 2 / (DeterminantMeasure.Construction.haarModulus ℂ b : ℝ) := by
  rw [complexCharacter, CharacterScaling.Construction.fourierHaarScaleSquared_mulShift _ _ hb,
    ComplexFourierStandard.Construction.fourierHaarScaleSquared_complex_standard]

theorem fourierHaarScaleSquared_complex_pos (b : ℂ) (hb : b ≠ 0) :
    0 < FunctionsMetaplectic.Construction.fourierHaarScaleSquared ℂ (complexCharacter b) := by
  rw [fourierHaarScaleSquared_complex b hb]
  exact div_pos (sq_pos_of_pos ArchimedeanTestSpace.Construction.complexReferenceHaarFactor_pos) (DeterminantMeasure.Construction.haarModulus_pos ℂ hb)

theorem selfDualMeasure_complex (b : ℂ) (hb : b ≠ 0) :
    FunctionsMetaplectic.Construction.selfDualMeasure ℂ (complexCharacter b) =
      ENNReal.ofReal (Real.sqrt (DeterminantMeasure.Construction.haarModulus ℂ b : ℝ)) • volume := by
  have hr : (ArchimedeanTestSpace.Construction.complexReferenceHaarFactor : ℝ) ≠ 0 :=
    (show (0 : ℝ) < ArchimedeanTestSpace.Construction.complexReferenceHaarFactor from ArchimedeanTestSpace.Construction.complexReferenceHaarFactor_pos).ne'
  have hs : Real.sqrt (DeterminantMeasure.Construction.haarModulus ℂ b : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (DeterminantMeasure.Construction.haarModulus_pos ℂ hb)).ne'
  have hscale : (Real.sqrt ((ArchimedeanTestSpace.Construction.complexReferenceHaarFactor : ℝ) ^ 2 /
      (DeterminantMeasure.Construction.haarModulus ℂ b : ℝ)))⁻¹ * (ArchimedeanTestSpace.Construction.complexReferenceHaarFactor : ℝ) =
      Real.sqrt (DeterminantMeasure.Construction.haarModulus ℂ b : ℝ) := by
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq ArchimedeanTestSpace.Construction.complexReferenceHaarFactor.coe_nonneg]
    field_simp
  rw [FunctionsMetaplectic.Construction.selfDualMeasure, fourierHaarScaleSquared_complex b hb,
    Measure.isAddLeftInvariant_eq_smul_of_regular (Measure.addHaar : Measure ℂ) volume]
  change ENNReal.ofReal (Real.sqrt ((ArchimedeanTestSpace.Construction.complexReferenceHaarFactor : ℝ) ^ 2 /
      (DeterminantMeasure.Construction.haarModulus ℂ b : ℝ)))⁻¹ • (ArchimedeanTestSpace.Construction.complexReferenceHaarFactor • volume) = _
  rw [ENNReal.smul_def, smul_smul]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity), hscale]

theorem positionMeasure_complex (n : ℕ) (b : ℂ) (hb : b ≠ 0) :
    FunctionsMetaplectic.Construction.positionMeasure ℂ n (complexCharacter b) =
      ENNReal.ofReal (Real.sqrt (DeterminantMeasure.Construction.haarModulus ℂ b : ℝ) ^ n) • volume := by
  unfold FunctionsMetaplectic.Construction.positionMeasure
  simp_rw [selfDualMeasure_complex b hb]
  let : (ENNReal.ofReal (Real.sqrt (DeterminantMeasure.Construction.haarModulus ℂ b : ℝ)) • (volume : Measure ℂ)).IsAddHaarMeasure := by
    apply Measure.IsAddHaarMeasure.smul
    · exact (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (DeterminantMeasure.Construction.haarModulus_pos ℂ hb))).ne'
    · exact ENNReal.ofReal_ne_top
  refine Measure.pi_eq (μ := fun _ : Fin n =>
    ENNReal.ofReal (Real.sqrt (DeterminantMeasure.Construction.haarModulus ℂ b : ℝ)) • (volume : Measure ℂ)) fun s _ => ?_
  rw [Measure.smul_apply, volume_pi_pi]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (Real.sqrt_nonneg _)]

theorem complex_fourier_square_volume (n : ℕ) (b : ℂ) (hb : b ≠ 0)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) (x : FunctionsMetaplectic.Construction.Position ℂ n) :
    FunctionsMetaplectic.Construction.fourierIntegral (complexCharacter b) volume
      (FunctionsMetaplectic.Construction.fourierIntegral (complexCharacter b) volume f.val) x =
      (((DeterminantMeasure.Construction.haarModulus ℂ b : ℝ) ^ n)⁻¹ : ℝ) • f.val (-x) := by
  have hf : FunctionsMetaplectic.Construction.fourierIntegral (complexCharacter b) volume f.val =
      fun y => FunctionsMetaplectic.Construction.fourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume f.val (b • y) :=
    funext (CharacterScaling.Construction.fourierIntegral_mulShift n ArchimedeanTestSpace.Construction.complexStandardCharacter b volume f.val)
  rw [hf]
  change FunctionsMetaplectic.Construction.fourierIntegral (ArchimedeanTestSpace.Construction.complexStandardCharacter.mulShift b) (Measure.pi (fun _ : Fin n => volume))
    (fun y => FunctionsMetaplectic.Construction.fourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume f.val (b • y)) x = _
  rw [CharacterScaling.Construction.fourierIntegral_mulShift_scaled_input _ _ _ hb]
  congr 1
  exact ComplexStandardNormalization.Construction.complex_fourier_inversion_standard n f x

theorem fourierIntegral_complex_normalized (n : ℕ) (b : ℂ) (hb : b ≠ 0)
    (f : FunctionsMetaplectic.Construction.Position ℂ n → ℂ) (x : FunctionsMetaplectic.Construction.Position ℂ n) :
    FunctionsMetaplectic.Construction.fourierIntegral (complexCharacter b) (FunctionsMetaplectic.Construction.positionMeasure ℂ n (complexCharacter b)) f x =
      (Real.sqrt (DeterminantMeasure.Construction.haarModulus ℂ b : ℝ) ^ n : ℝ) • FunctionsMetaplectic.Construction.fourierIntegral (complexCharacter b) volume f x := by
  rw [positionMeasure_complex n b hb, FunctionsMetaplectic.Construction.fourierIntegral, integral_smul_measure]
  rw [ENNReal.toReal_ofReal (by positivity)]
  rfl

theorem complex_fourier_inversion (n : ℕ) (b : ℂ) (hb : b ≠ 0)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) (x : FunctionsMetaplectic.Construction.Position ℂ n) :
    FunctionsMetaplectic.Construction.fourierIntegral (complexCharacter b) (FunctionsMetaplectic.Construction.positionMeasure ℂ n (complexCharacter b))
      (FunctionsMetaplectic.Construction.fourierIntegral (complexCharacter b) (FunctionsMetaplectic.Construction.positionMeasure ℂ n (complexCharacter b)) f.val) x =
        f.val (-x) := by
  let c : ℝ := DeterminantMeasure.Construction.haarModulus ℂ b
  have hc : 0 < c := DeterminantMeasure.Construction.haarModulus_pos ℂ hb
  have hf : FunctionsMetaplectic.Construction.fourierIntegral (complexCharacter b) (FunctionsMetaplectic.Construction.positionMeasure ℂ n (complexCharacter b)) f.val =
      (Real.sqrt c ^ n : ℂ) • FunctionsMetaplectic.Construction.fourierIntegral (complexCharacter b) volume f.val := by
    funext y
    rw [fourierIntegral_complex_normalized n b hb]
    simp only [c, Complex.real_smul, Pi.smul_apply, smul_eq_mul, Complex.ofReal_pow]
  rw [fourierIntegral_complex_normalized n b hb, hf, FunctionsMetaplectic.Construction.fourierIntegral_smul,
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

theorem complex_fourier_mem (n : ℕ) (b : ℂ) (hb : b ≠ 0) (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) :
    FunctionsMetaplectic.Construction.fourierIntegral (complexCharacter b) (FunctionsMetaplectic.Construction.positionMeasure ℂ n (complexCharacter b)) f.val ∈
      FunctionsMetaplectic.Construction.schwartzBruhat ℂ n := by
  obtain ⟨φ, hφ⟩ := ArchimedeanTestSpace.Construction.schwartzBruhat_archimedean_iff.mp (ComplexStandardNormalization.Construction.complex_fourier_mem_standard n f)
  let e := (CharacterScaling.Construction.scalarPositionEquiv n b hb).restrictScalars ℝ
  let χ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e φ
  refine ArchimedeanTestSpace.Construction.schwartzBruhat_archimedean_iff.mpr
    ⟨(Real.sqrt (DeterminantMeasure.Construction.haarModulus ℂ b : ℝ) ^ n : ℂ) • χ, ?_⟩
  funext x
  rw [fourierIntegral_complex_normalized n b hb, complexCharacter, CharacterScaling.Construction.fourierIntegral_mulShift, hφ]
  change (Real.sqrt (DeterminantMeasure.Construction.haarModulus ℂ b : ℝ) ^ n : ℝ) • φ (b • x) =
    (Real.sqrt (DeterminantMeasure.Construction.haarModulus ℂ b : ℝ) ^ n : ℂ) * φ (b • x)
  simp only [Complex.real_smul, Complex.ofReal_pow]

theorem complex_fourier_analysis (n : ℕ)
    (ψ : AddChar ℂ ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1) :
    0 < FunctionsMetaplectic.Construction.fourierHaarScaleSquared ℂ ψ ∧
    (∀ f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n,
      FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ) f.val ∈ FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) ∧
    ∀ (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) x,
      FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ)
        (FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ) f.val) x = f.val (-x) := by
  obtain ⟨b, hbn, rfl⟩ := continuous_nontrivial_unitary_complex_character ψ hc hu hn
  exact ⟨fourierHaarScaleSquared_complex_pos b hbn, complex_fourier_mem n b hbn,
    complex_fourier_inversion n b hbn⟩

end

end OAI.RepresentationTheory.Weil.Local.ComplexNormalization.Construction
