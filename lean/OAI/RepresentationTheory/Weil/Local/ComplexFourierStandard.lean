import OAI.RepresentationTheory.Weil.Local.ArchimedeanTestSpace
import OAI.RepresentationTheory.Weil.Local.RealFourierLp
import OAI.RepresentationTheory.Weil.Local.FourierTensor

/-! # Complex Fourier Standard -/

namespace OAI.RepresentationTheory.Weil.Local.ComplexFourierStandard.Construction

noncomputable section

section

/-! Exact reference-set Fourier normalization for the standard complex character. -/

open _root_.MeasureTheory
open scoped FourierTransform ComplexConjugate NNReal

theorem scalarFourierIntegral_complex_standard (f : ℂ → ℂ) (x : ℂ) :
    FourierTensor.Construction.scalarFourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume f x = 𝓕 f (conj x) := by
  rw [Real.fourier_eq]
  unfold FourierTensor.Construction.scalarFourierIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    have hi : @inner ℝ ℂ _ t (conj x) = (x * t).re := by
      rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply]
      simp [Complex.mul_re, mul_comm]
    dsimp only
    rw [hi]
    change f t * Gaussian.Construction.realCharacter 1 (-(x * t)).re = (Real.fourierChar (-(x * t).re) : ℂ) • f t
    simp only [Complex.neg_re, Gaussian.Construction.realCharacter, MonoidHom.compAddChar_apply,
      AddChar.mulShift_apply, one_mul, Function.comp_apply, smul_eq_mul]
    exact mul_comm _ _

theorem scalarFourierIntegral_indicator {k : Type} [Field k] [MeasurableSpace k]
    (ψ : AddChar k ℂ) (μ : Measure k) (S : Set k) (hS : MeasurableSet S) (x : k) :
    FourierTensor.Construction.scalarFourierIntegral ψ μ (S.indicator (fun _ => (1 : ℂ))) x = ∫ t in S, ψ (-(x * t)) ∂μ := by
  rw [FourierTensor.Construction.scalarFourierIntegral, ← integral_indicator hS]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    by_cases ht : t ∈ S <;> simp [ht]

theorem referenceFourier_complex_standard (x : ℂ) :
    FunctionsMetaplectic.Construction.referenceFourier ℂ ArchimedeanTestSpace.Construction.complexStandardCharacter x =
      (ArchimedeanTestSpace.Construction.complexReferenceHaarFactor : ℂ) *
        𝓕 ((FunctionsMetaplectic.Construction.referenceCompact ℂ : Set ℂ).indicator (fun _ => (1 : ℂ))) (conj x) := by
  rw [FunctionsMetaplectic.Construction.referenceFourier, Measure.isAddLeftInvariant_eq_smul_of_regular
    (Measure.addHaar : Measure ℂ) volume, Measure.restrict_smul, integral_smul_nnreal_measure]
  change (ArchimedeanTestSpace.Construction.complexReferenceHaarFactor : ℂ) * _ = _
  congr 1
  rw [← scalarFourierIntegral_indicator _ _ _ (FunctionsMetaplectic.Construction.referenceCompact ℂ).isCompact.measurableSet,
    scalarFourierIntegral_complex_standard]

theorem fourierHaarScaleSquared_complex_standard :
    FunctionsMetaplectic.Construction.fourierHaarScaleSquared ℂ ArchimedeanTestSpace.Construction.complexStandardCharacter = (ArchimedeanTestSpace.Construction.complexReferenceHaarFactor : ℝ) ^ 2 := by
  let r : ℝ := ArchimedeanTestSpace.Construction.complexReferenceHaarFactor
  let S : Set ℂ := FunctionsMetaplectic.Construction.referenceCompact ℂ
  have hr : r ≠ 0 := (show 0 < r from ArchimedeanTestSpace.Construction.complexReferenceHaarFactor_pos).ne'
  have hSpos : 0 < volume.real S := by
    apply ENNReal.toReal_pos
    · exact (Measure.measure_pos_of_nonempty_interior volume (FunctionsMetaplectic.Construction.referenceCompact ℂ).interior_nonempty).ne'
    · exact (FunctionsMetaplectic.Construction.referenceCompact ℂ).isCompact.measure_ne_top
  have hhaar : (Measure.addHaar : Measure ℂ) = ArchimedeanTestSpace.Construction.complexReferenceHaarFactor • volume :=
    Measure.isAddLeftInvariant_eq_smul_of_regular _ _
  have hconj : (∫ x : ℂ, ‖𝓕 (S.indicator (fun _ => (1 : ℂ))) (conj x)‖ ^ 2) =
      ∫ x : ℂ, ‖𝓕 (S.indicator (fun _ => (1 : ℂ))) x‖ ^ 2 := by
    simpa using! Complex.conjLIE.measurePreserving.integral_comp
      Complex.conjLIE.toHomeomorph.measurableEmbedding
      (fun x => ‖𝓕 (S.indicator (fun _ => (1 : ℂ))) x‖ ^ 2)
  have hS : volume.real S ≠ 0 := hSpos.ne'
  unfold FunctionsMetaplectic.Construction.fourierHaarScaleSquared
  simp_rw [referenceFourier_complex_standard, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ArchimedeanTestSpace.Construction.complexReferenceHaarFactor.coe_nonneg, mul_pow]
  rw [hhaar, integral_smul_nnreal_measure, measureReal_nnreal_smul_apply]
  simp only [NNReal.smul_def, smul_eq_mul]
  rw [integral_const_mul, hconj, RealFourierLp.Construction.real_indicator_fourier_norm_sq
    (FunctionsMetaplectic.Construction.referenceCompact ℂ).isCompact.measurableSet (FunctionsMetaplectic.Construction.referenceCompact ℂ).isCompact.measure_ne_top]
  change (r * (r ^ 2 * volume.real S)) / (r * volume.real S) = r ^ 2
  field_simp

theorem selfDualMeasure_complex_standard : FunctionsMetaplectic.Construction.selfDualMeasure ℂ ArchimedeanTestSpace.Construction.complexStandardCharacter = volume := by
  have hr : ArchimedeanTestSpace.Construction.complexReferenceHaarFactor ≠ 0 := ArchimedeanTestSpace.Construction.complexReferenceHaarFactor_pos.ne'
  rw [FunctionsMetaplectic.Construction.selfDualMeasure, fourierHaarScaleSquared_complex_standard,
    Real.sqrt_sq ArchimedeanTestSpace.Construction.complexReferenceHaarFactor.coe_nonneg]
  rw [Measure.isAddLeftInvariant_eq_smul_of_regular (Measure.addHaar : Measure ℂ) volume]
  change ENNReal.ofReal ((ArchimedeanTestSpace.Construction.complexReferenceHaarFactor : ℝ)⁻¹) •
    (ArchimedeanTestSpace.Construction.complexReferenceHaarFactor • volume) = volume
  rw [← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal, ← ENNReal.smul_def,
    smul_smul, inv_mul_cancel₀ hr, one_smul]

end

/-! Complex Fourier analysis in arbitrary rank. Haar uniqueness first gives
an explicit scalar; a tensor test determines that scalar exactly. -/

open _root_.MeasureTheory
open scoped FourierTransform ComplexConjugate NNReal SchwartzMap ContDiff

section Twist
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def twistedSchwartzFourier (J : E ≃ₗᵢ[ℝ] E) (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ J.toContinuousLinearEquiv (𝓕 f)

theorem twistedSchwartzFourier_apply (J : E ≃ₗᵢ[ℝ] E) (f : SchwartzMap E ℂ) (x : E) :
    twistedSchwartzFourier J f x = 𝓕 (f : E → ℂ) (J x) := by
  exact congrFun (SchwartzMap.fourier_coe f) (J x)

theorem realSchwartz_fourier_square (f : SchwartzMap E ℂ) (x : E) :
    𝓕 (𝓕 (f : E → ℂ)) x = f (-x) := by
  have h := congrArg (fun g : SchwartzMap E ℂ => g (-x))
    ((FourierTransform.fourierEquiv ℂ (SchwartzMap E ℂ)).symm_apply_apply f)
  change 𝓕⁻ (𝓕 f : SchwartzMap E ℂ) (-x) = f (-x) at h
  simp only [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe] at h
  rwa [Real.fourierInv_eq_fourier_neg, neg_neg] at h

theorem twistedSchwartzFourier_square (J : E ≃ₗᵢ[ℝ] E)
    (hJ : Function.Involutive J) (f : SchwartzMap E ℂ) (x : E) :
    twistedSchwartzFourier J (twistedSchwartzFourier J f) x = f (-x) := by
  rw [twistedSchwartzFourier_apply]
  have hf : (twistedSchwartzFourier J f : E → ℂ) = 𝓕 (f : E → ℂ) ∘ J :=
    funext (twistedSchwartzFourier_apply J f)
  rw [hf, Real.fourier_comp_linearIsometry, hJ, realSchwartz_fourier_square]

end Twist

theorem scalarFourierIntegral_complex_standard_square (f : SchwartzMap ℂ ℂ) (x : ℂ) :
    FourierTensor.Construction.scalarFourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume
      (FourierTensor.Construction.scalarFourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume f) x = f (-x) := by
  have hf : FourierTensor.Construction.scalarFourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume f =
      (twistedSchwartzFourier Complex.conjLIE f : ℂ → ℂ) := by
    funext y
    rw [scalarFourierIntegral_complex_standard, twistedSchwartzFourier_apply]
    rfl
  rw [hf, scalarFourierIntegral_complex_standard]
  exact twistedSchwartzFourier_square Complex.conjLIE (fun _ => star_star _) f x

def complexL2Coordinates (n : ℕ) : EuclideanSpace ℂ (Fin n) ≃L[ℝ] FunctionsMetaplectic.Construction.Position ℂ n :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)

def complexPositionHaar (n : ℕ) : Measure (EuclideanSpace ℂ (Fin n)) :=
  (volume : Measure (FunctionsMetaplectic.Construction.Position ℂ n)).map (complexL2Coordinates n).symm

instance complexPositionHaar_isAddHaarMeasure (n : ℕ) : (complexPositionHaar n).IsAddHaarMeasure :=
  (complexL2Coordinates n).symm.isAddHaarMeasure_map volume

def complexPositionHaarFactor (n : ℕ) : ℝ≥0 :=
  Measure.addHaarScalarFactor (complexPositionHaar n) volume

theorem complexPositionHaar_eq (n : ℕ) :
    complexPositionHaar n = complexPositionHaarFactor n • volume :=
  Measure.isAddLeftInvariant_eq_smul_of_regular _ _

def complexConjugation (n : ℕ) : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin n => Complex.conjLIE)

theorem complexConjugation_involutive (n : ℕ) : Function.Involutive (complexConjugation n) := by
  intro x
  ext i
  exact star_star (x i)

theorem complex_inner_conjugation (n : ℕ) (x y : EuclideanSpace ℂ (Fin n)) :
    @inner ℝ (EuclideanSpace ℂ (Fin n)) _ y (complexConjugation n x) =
      (FunctionsMetaplectic.Construction.dot (complexL2Coordinates n x) (complexL2Coordinates n y)).re := by
  rw [PiLp.inner_apply]
  change (∑ i, @inner ℝ ℂ _ (y i) (conj (x i))) = (∑ i, x i * y i).re
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply]
  simp [Complex.mul_re]

theorem complex_fourier_coordinates (n : ℕ) (f : FunctionsMetaplectic.Construction.Position ℂ n → ℂ) (x : FunctionsMetaplectic.Construction.Position ℂ n) :
    FunctionsMetaplectic.Construction.fourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume f x =
      (complexPositionHaarFactor n : ℂ) *
        𝓕 (f ∘ complexL2Coordinates n) (complexConjugation n ((complexL2Coordinates n).symm x)) := by
  have hmap := integral_map_equiv (μ := (volume : Measure (FunctionsMetaplectic.Construction.Position ℂ n)))
    (complexL2Coordinates n).symm.toHomeomorph.toMeasurableEquiv
    (fun y => f (complexL2Coordinates n y) *
      ArchimedeanTestSpace.Construction.complexStandardCharacter (-(FunctionsMetaplectic.Construction.dot x (complexL2Coordinates n y))))
  have heq : FunctionsMetaplectic.Construction.fourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume f x =
      ∫ y, f (complexL2Coordinates n y) *
        ArchimedeanTestSpace.Construction.complexStandardCharacter (-(FunctionsMetaplectic.Construction.dot x (complexL2Coordinates n y))) ∂ complexPositionHaar n := by
    simpa [FunctionsMetaplectic.Construction.fourierIntegral, complexPositionHaar] using! hmap.symm
  rw [heq, complexPositionHaar_eq, integral_smul_nnreal_measure]
  change (complexPositionHaarFactor n : ℂ) * _ = _
  congr 1
  rw [Real.fourier_eq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only [Function.comp_apply]
    rw [complex_inner_conjugation, ContinuousLinearEquiv.apply_symm_apply]
    change f (complexL2Coordinates n y) * Gaussian.Construction.realCharacter 1 (-(FunctionsMetaplectic.Construction.dot x (complexL2Coordinates n y))).re = _
    simp only [Complex.neg_re, Gaussian.Construction.realCharacter, MonoidHom.compAddChar_apply,
      AddChar.mulShift_apply, one_mul, Function.comp_apply, Circle.smul_def, smul_eq_mul]
    exact mul_comm _ _

def complexSchwartzFourier (n : ℕ) (f : SchwartzMap (FunctionsMetaplectic.Construction.Position ℂ n) ℂ) :
    SchwartzMap (FunctionsMetaplectic.Construction.Position ℂ n) ℂ :=
  (complexPositionHaarFactor n : ℂ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (complexL2Coordinates n).symm
      (twistedSchwartzFourier (complexConjugation n)
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (complexL2Coordinates n) f))

theorem complexSchwartzFourier_apply (n : ℕ) (f : SchwartzMap (FunctionsMetaplectic.Construction.Position ℂ n) ℂ)
    (x : FunctionsMetaplectic.Construction.Position ℂ n) :
    complexSchwartzFourier n f x = FunctionsMetaplectic.Construction.fourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume f x := by
  rw [complex_fourier_coordinates]
  change (complexPositionHaarFactor n : ℂ) * _ = _
  congr 1

theorem complexSchwartzFourier_square (n : ℕ) (f : SchwartzMap (FunctionsMetaplectic.Construction.Position ℂ n) ℂ)
    (x : FunctionsMetaplectic.Construction.Position ℂ n) :
    complexSchwartzFourier n (complexSchwartzFourier n f) x =
      (complexPositionHaarFactor n : ℂ) ^ 2 * f (-x) := by
  let e := complexL2Coordinates n
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f
  have he : SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (complexSchwartzFourier n f) =
      (complexPositionHaarFactor n : ℂ) • twistedSchwartzFourier (complexConjugation n) g := by
    ext y
    change (complexPositionHaarFactor n : ℂ) *
      twistedSchwartzFourier (complexConjugation n) g (e.symm (e y)) =
      (complexPositionHaarFactor n : ℂ) * twistedSchwartzFourier (complexConjugation n) g y
    rw [ContinuousLinearEquiv.symm_apply_apply]
  change (complexPositionHaarFactor n : ℂ) *
    twistedSchwartzFourier (complexConjugation n)
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (complexSchwartzFourier n f)) (e.symm x) = _
  rw [he]
  simp only [twistedSchwartzFourier, FourierTransform.fourier_smul,
    map_smul, smul_apply, smul_eq_mul]
  change (complexPositionHaarFactor n : ℂ) * ((complexPositionHaarFactor n : ℂ) *
    twistedSchwartzFourier (complexConjugation n)
      (twistedSchwartzFourier (complexConjugation n) g) (e.symm x)) = _
  rw [twistedSchwartzFourier_square _ (complexConjugation_involutive n)]
  change (complexPositionHaarFactor n : ℂ) * ((complexPositionHaarFactor n : ℂ) *
    f (e (-e.symm x))) = _
  rw [map_neg, ContinuousLinearEquiv.apply_symm_apply]
  ring

end

end OAI.RepresentationTheory.Weil.Local.ComplexFourierStandard.Construction
