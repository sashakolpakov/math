import OAI.RepresentationTheory.Weil.AdelicSplitting.RealCharacters
import OAI.RepresentationTheory.Weil.AdelicSplitting.TensorFourier

/-! # Complex Fourier -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ComplexFourier.LocalAnalysis

noncomputable section

section

/-! The complex standard character and its exact reference-set Haar
normalization, computed through the real Fourier transform on ℂ. -/

open _root_.MeasureTheory
open scoped FourierTransform ComplexConjugate NNReal

def complexStandardCharacter : AddChar ℂ ℂ :=
  (RealCharacters.LocalAnalysis.realCharacter 1).compAddMonoidHom Complex.reCLM.toLinearMap.toAddMonoidHom

theorem continuous_unitary_complex_character
    (ψ : AddChar ℂ ℂ) (hc : Continuous ψ) (hu : ∀ z, ‖ψ z‖ = 1) :
    ∃ a b : ℝ, ∀ z : ℂ, ψ z = RealCharacters.LocalAnalysis.realCharacter a z.re * RealCharacters.LocalAnalysis.realCharacter b z.im := by
  let r : AddChar ℝ ℂ := ψ.compAddMonoidHom Complex.ofRealHom.toAddMonoidHom
  let i : AddChar ℝ ℂ := ψ.compAddMonoidHom
    ((AddMonoidHom.mulRight Complex.I).comp Complex.ofRealHom.toAddMonoidHom)
  have hr : Continuous r := hc.comp Complex.continuous_ofReal
  have hi : Continuous i := hc.comp (Complex.continuous_ofReal.mul_const Complex.I)
  obtain ⟨a, ha⟩ := RealCharacters.LocalAnalysis.continuous_unitary_real_character r hr (fun t => hu (t : ℂ))
  obtain ⟨b, hb⟩ := RealCharacters.LocalAnalysis.continuous_unitary_real_character i hi (fun t => hu ((t : ℂ) * Complex.I))
  refine ⟨a, b, fun z => ?_⟩
  rw [← ha, ← hb]
  change ψ z = ψ (z.re : ℂ) * ψ ((z.im : ℂ) * Complex.I)
  rw [← ψ.map_add_eq_mul, Complex.re_add_im]

theorem complex_character_coefficient
    (ψ : AddChar ℂ ℂ) (hc : Continuous ψ) (hu : ∀ z, ‖ψ z‖ = 1) :
    ∃ b : ℂ, ∀ z : ℂ, ψ z = complexStandardCharacter (b * z) := by
  obtain ⟨r, s, h⟩ := continuous_unitary_complex_character ψ hc hu
  refine ⟨(r : ℂ) - (s : ℂ) * Complex.I, fun z => ?_⟩
  rw [h]
  change RealCharacters.LocalAnalysis.realCharacter r z.re * RealCharacters.LocalAnalysis.realCharacter s z.im =
    RealCharacters.LocalAnalysis.realCharacter 1 ((((r : ℂ) - (s : ℂ) * Complex.I) * z).re)
  rw [RealCharacters.LocalAnalysis.realCharacter_apply, RealCharacters.LocalAnalysis.realCharacter_apply, RealCharacters.LocalAnalysis.realCharacter_apply, ← Complex.exp_add]
  congr 1
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, sub_zero,
    Complex.sub_im, Complex.mul_im, mul_one, zero_sub]
  push_cast
  ring

theorem scalarFourier_complex_standard (f : ℂ → ℂ) (x : ℂ) :
    TensorFourier.LocalAnalysis.scalarFourier complexStandardCharacter volume f x = 𝓕 f (conj x) := by
  rw [Real.fourier_eq]
  unfold TensorFourier.LocalAnalysis.scalarFourier
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    have hi : @inner ℝ ℂ _ t (conj x) = (x * t).re := by
      rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply]
      simp [Complex.mul_re, mul_comm]
    dsimp only
    rw [hi]
    change f t * RealCharacters.LocalAnalysis.realCharacter 1 (-(x * t)).re = (Real.fourierChar (-(x * t).re) : ℂ) • f t
    simp only [Complex.neg_re, RealCharacters.LocalAnalysis.realCharacter, MonoidHom.compAddChar_apply,
      AddChar.mulShift_apply, one_mul, Function.comp_apply, smul_eq_mul]
    exact mul_comm _ _

theorem scalarFourier_indicator {k : Type} [Field k] [MeasurableSpace k]
    (ψ : AddChar k ℂ) (μ : Measure k) (S : Set k) (hS : MeasurableSet S) (x : k) :
    TensorFourier.LocalAnalysis.scalarFourier ψ μ (S.indicator (fun _ => (1 : ℂ))) x = ∫ t in S, ψ (-(x * t)) ∂μ := by
  rw [TensorFourier.LocalAnalysis.scalarFourier, ← integral_indicator hS]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    by_cases ht : t ∈ S <;> simp [ht]

def complexReferenceHaarFactor : ℝ≥0 :=
  Measure.addHaarScalarFactor (Measure.addHaar : Measure ℂ) volume

theorem complexReferenceHaarFactor_pos : 0 < complexReferenceHaarFactor :=
  Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

theorem referenceFourier_complex_standard (x : ℂ) :
    Local.FunctionsMetaplectic.Construction.referenceFourier ℂ complexStandardCharacter x =
      (complexReferenceHaarFactor : ℂ) *
        𝓕 ((Local.FunctionsMetaplectic.Construction.referenceCompact ℂ : Set ℂ).indicator (fun _ => (1 : ℂ))) (conj x) := by
  rw [Local.FunctionsMetaplectic.Construction.referenceFourier, Measure.isAddLeftInvariant_eq_smul_of_regular
    (Measure.addHaar : Measure ℂ) volume, Measure.restrict_smul, integral_smul_nnreal_measure]
  change (complexReferenceHaarFactor : ℂ) * _ = _
  congr 1
  rw [← scalarFourier_indicator _ _ _ (Local.FunctionsMetaplectic.Construction.referenceCompact ℂ).isCompact.measurableSet,
    scalarFourier_complex_standard]

theorem fourierHaarScaleSquared_complex_standard :
    Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared ℂ complexStandardCharacter = (complexReferenceHaarFactor : ℝ) ^ 2 := by
  let r : ℝ := complexReferenceHaarFactor
  let S : Set ℂ := Local.FunctionsMetaplectic.Construction.referenceCompact ℂ
  have hr : r ≠ 0 := (show 0 < r from complexReferenceHaarFactor_pos).ne'
  have hSpos : 0 < volume.real S := by
    apply ENNReal.toReal_pos
    · exact (Measure.measure_pos_of_nonempty_interior volume (Local.FunctionsMetaplectic.Construction.referenceCompact ℂ).interior_nonempty).ne'
    · exact (Local.FunctionsMetaplectic.Construction.referenceCompact ℂ).isCompact.measure_ne_top
  have hhaar : (Measure.addHaar : Measure ℂ) = complexReferenceHaarFactor • volume :=
    Measure.isAddLeftInvariant_eq_smul_of_regular _ _
  have hconj : (∫ x : ℂ, ‖𝓕 (S.indicator (fun _ => (1 : ℂ))) (conj x)‖ ^ 2) =
      ∫ x : ℂ, ‖𝓕 (S.indicator (fun _ => (1 : ℂ))) x‖ ^ 2 := by
    simpa using! Complex.conjLIE.measurePreserving.integral_comp
      Complex.conjLIE.toHomeomorph.measurableEmbedding
      (fun x => ‖𝓕 (S.indicator (fun _ => (1 : ℂ))) x‖ ^ 2)
  have hS : volume.real S ≠ 0 := hSpos.ne'
  unfold Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared
  simp_rw [referenceFourier_complex_standard, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg complexReferenceHaarFactor.coe_nonneg, mul_pow]
  rw [hhaar, integral_smul_nnreal_measure, measureReal_nnreal_smul_apply]
  simp only [NNReal.smul_def, smul_eq_mul]
  rw [integral_const_mul, hconj, RealCharacters.LocalAnalysis.real_indicator_fourier_norm_sq
    (Local.FunctionsMetaplectic.Construction.referenceCompact ℂ).isCompact.measurableSet (Local.FunctionsMetaplectic.Construction.referenceCompact ℂ).isCompact.measure_ne_top]
  change (r * (r ^ 2 * volume.real S)) / (r * volume.real S) = r ^ 2
  field_simp

theorem selfDualMeasure_complex_standard : Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ complexStandardCharacter = volume := by
  have hr : complexReferenceHaarFactor ≠ 0 := complexReferenceHaarFactor_pos.ne'
  rw [Local.FunctionsMetaplectic.Construction.selfDualMeasure, fourierHaarScaleSquared_complex_standard,
    Real.sqrt_sq complexReferenceHaarFactor.coe_nonneg]
  rw [Measure.isAddLeftInvariant_eq_smul_of_regular (Measure.addHaar : Measure ℂ) volume]
  change ENNReal.ofReal ((complexReferenceHaarFactor : ℝ)⁻¹) •
    (complexReferenceHaarFactor • volume) = volume
  rw [← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal, ← ENNReal.smul_def,
    smul_smul, inv_mul_cancel₀ hr, one_smul]

end

section

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

theorem scalarFourier_complex_standard_square (f : SchwartzMap ℂ ℂ) (x : ℂ) :
    TensorFourier.LocalAnalysis.scalarFourier complexStandardCharacter volume
      (TensorFourier.LocalAnalysis.scalarFourier complexStandardCharacter volume f) x = f (-x) := by
  have hf : TensorFourier.LocalAnalysis.scalarFourier complexStandardCharacter volume f =
      (twistedSchwartzFourier Complex.conjLIE f : ℂ → ℂ) := by
    funext y
    rw [scalarFourier_complex_standard, twistedSchwartzFourier_apply]
    rfl
  rw [hf, scalarFourier_complex_standard]
  exact twistedSchwartzFourier_square Complex.conjLIE (fun _ => star_star _) f x

def complexL2Coordinates (n : ℕ) : EuclideanSpace ℂ (Fin n) ≃L[ℝ] Local.FunctionsMetaplectic.Construction.Position ℂ n :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)

def complexPositionHaar (n : ℕ) : Measure (EuclideanSpace ℂ (Fin n)) :=
  (volume : Measure (Local.FunctionsMetaplectic.Construction.Position ℂ n)).map (complexL2Coordinates n).symm

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
      (Local.FunctionsMetaplectic.Construction.dot (complexL2Coordinates n x) (complexL2Coordinates n y)).re := by
  rw [PiLp.inner_apply]
  change (∑ i, @inner ℝ ℂ _ (y i) (conj (x i))) = (∑ i, x i * y i).re
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply]
  simp [Complex.mul_re]

theorem complex_fourier_coordinates (n : ℕ) (f : Local.FunctionsMetaplectic.Construction.Position ℂ n → ℂ) (x : Local.FunctionsMetaplectic.Construction.Position ℂ n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral complexStandardCharacter volume f x =
      (complexPositionHaarFactor n : ℂ) *
        𝓕 (f ∘ complexL2Coordinates n) (complexConjugation n ((complexL2Coordinates n).symm x)) := by
  have hmap := integral_map_equiv (μ := (volume : Measure (Local.FunctionsMetaplectic.Construction.Position ℂ n)))
    (complexL2Coordinates n).symm.toHomeomorph.toMeasurableEquiv
    (fun y => f (complexL2Coordinates n y) *
      complexStandardCharacter (-(Local.FunctionsMetaplectic.Construction.dot x (complexL2Coordinates n y))))
  have heq : Local.FunctionsMetaplectic.Construction.fourierIntegral complexStandardCharacter volume f x =
      ∫ y, f (complexL2Coordinates n y) *
        complexStandardCharacter (-(Local.FunctionsMetaplectic.Construction.dot x (complexL2Coordinates n y))) ∂ complexPositionHaar n := by
    simpa [Local.FunctionsMetaplectic.Construction.fourierIntegral, complexPositionHaar] using! hmap.symm
  rw [heq, complexPositionHaar_eq, integral_smul_nnreal_measure]
  change (complexPositionHaarFactor n : ℂ) * _ = _
  congr 1
  rw [Real.fourier_eq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only [Function.comp_apply]
    rw [complex_inner_conjugation, ContinuousLinearEquiv.apply_symm_apply]
    change f (complexL2Coordinates n y) * RealCharacters.LocalAnalysis.realCharacter 1 (-(Local.FunctionsMetaplectic.Construction.dot x (complexL2Coordinates n y))).re = _
    simp only [Complex.neg_re, RealCharacters.LocalAnalysis.realCharacter, MonoidHom.compAddChar_apply,
      AddChar.mulShift_apply, one_mul, Function.comp_apply, Circle.smul_def, smul_eq_mul]
    exact mul_comm _ _

def complexSchwartzFourier (n : ℕ) (f : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℂ n) ℂ) :
    SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℂ n) ℂ :=
  (complexPositionHaarFactor n : ℂ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (complexL2Coordinates n).symm
      (twistedSchwartzFourier (complexConjugation n)
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (complexL2Coordinates n) f))

theorem complexSchwartzFourier_apply (n : ℕ) (f : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℂ n) ℂ)
    (x : Local.FunctionsMetaplectic.Construction.Position ℂ n) :
    complexSchwartzFourier n f x = Local.FunctionsMetaplectic.Construction.fourierIntegral complexStandardCharacter volume f x := by
  rw [complex_fourier_coordinates]
  change (complexPositionHaarFactor n : ℂ) * _ = _
  congr 1

theorem complexSchwartzFourier_square (n : ℕ) (f : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℂ n) ℂ)
    (x : Local.FunctionsMetaplectic.Construction.Position ℂ n) :
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

/-! Tensor calibration of complex Fourier inversion for the actual product
of the prescribed one-dimensional self-dual measures. -/

open _root_.MeasureTheory
open scoped FourierTransform ComplexConjugate NNReal SchwartzMap ContDiff

theorem complex_fourier_square_with_factor (n : ℕ)
    (f : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℂ n) ℂ) (x : Local.FunctionsMetaplectic.Construction.Position ℂ n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral complexStandardCharacter volume
      (Local.FunctionsMetaplectic.Construction.fourierIntegral complexStandardCharacter volume f) x =
      (complexPositionHaarFactor n : ℂ) ^ 2 * f (-x) := by
  have hf : (complexSchwartzFourier n f : Local.FunctionsMetaplectic.Construction.Position ℂ n → ℂ) =
      Local.FunctionsMetaplectic.Construction.fourierIntegral complexStandardCharacter volume f :=
    funext (complexSchwartzFourier_apply n f)
  rw [← hf, ← complexSchwartzFourier_apply, complexSchwartzFourier_square]

theorem complexPositionHaarFactor_one (n : ℕ) : complexPositionHaarFactor n = 1 := by
  let b : ContDiffBump (0 : ℂ) := default
  let φ : ℂ → ℂ := fun z => (b z : ℂ)
  have hφs : HasCompactSupport φ := b.hasCompactSupport.comp_left (show ((0 : ℝ) : ℂ) = 0 from rfl)
  have hφc : ContDiff ℝ ∞ φ := Complex.ofRealCLM.contDiff.comp b.contDiff
  let f : SchwartzMap ℂ ℂ := hφs.toSchwartzMap hφc
  have hf0 : f 0 = 1 := by
    change (b 0 : ℂ) = 1
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
    rfl
  have htc : ContDiff ℝ ∞ (TensorFourier.LocalAnalysis.tensorFunction n φ) := by
    apply contDiff_prod
    intro i _
    exact hφc.comp (ContinuousLinearMap.proj i : Local.FunctionsMetaplectic.Construction.Position ℂ n →L[ℝ] ℂ).contDiff
  let g : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℂ n) ℂ :=
    (TensorFourier.LocalAnalysis.tensorFunction_compactSupport n hφs).toSchwartzMap htc
  have he := complex_fourier_square_with_factor n g 0
  have hg0 : g (-0) = 1 := by
    have hφ0 : φ 0 = 1 := hf0
    simp [g, TensorFourier.LocalAnalysis.tensorFunction, hφ0]
  rw [hg0, mul_one] at he
  change Local.FunctionsMetaplectic.Construction.fourierIntegral complexStandardCharacter (Measure.pi (fun _ : Fin n => volume))
    (Local.FunctionsMetaplectic.Construction.fourierIntegral complexStandardCharacter (Measure.pi (fun _ : Fin n => volume))
      (TensorFourier.LocalAnalysis.tensorFunction n f)) 0 = (complexPositionHaarFactor n : ℂ) ^ 2 at he
  rw [TensorFourier.LocalAnalysis.fourierIntegral_tensorFunction, TensorFourier.LocalAnalysis.fourierIntegral_tensorFunction] at he
  change (∏ _ : Fin n, TensorFourier.LocalAnalysis.scalarFourier complexStandardCharacter volume
    (TensorFourier.LocalAnalysis.scalarFourier complexStandardCharacter volume f) 0) = _ at he
  simp only [scalarFourier_complex_standard_square, neg_zero, hf0, Finset.prod_const_one] at he
  have hr : (complexPositionHaarFactor n : ℝ) ^ 2 = 1 ^ 2 := by
    simpa only [one_pow] using (show (complexPositionHaarFactor n : ℝ) ^ 2 = 1 by exact_mod_cast he.symm)
  have h := (sq_eq_sq₀ (complexPositionHaarFactor n).coe_nonneg (by norm_num)).mp hr
  exact NNReal.coe_injective h

theorem complex_fourier_inversion_standard (n : ℕ)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) (x : Local.FunctionsMetaplectic.Construction.Position ℂ n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral complexStandardCharacter volume
      (Local.FunctionsMetaplectic.Construction.fourierIntegral complexStandardCharacter volume f.val) x = f.val (-x) := by
  obtain ⟨φ, hφ⟩ := ArchimedeanCharacters.LocalAnalysis.schwartzBruhat_archimedean_iff.mp f.property
  rw [hφ, complex_fourier_square_with_factor, complexPositionHaarFactor_one]
  simp

theorem complex_fourier_mem_standard (n : ℕ) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral complexStandardCharacter volume f.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat ℂ n := by
  obtain ⟨φ, hφ⟩ := ArchimedeanCharacters.LocalAnalysis.schwartzBruhat_archimedean_iff.mp f.property
  refine ArchimedeanCharacters.LocalAnalysis.schwartzBruhat_archimedean_iff.mpr ⟨complexSchwartzFourier n φ, ?_⟩
  rw [hφ]
  exact (funext (complexSchwartzFourier_apply n φ)).symm

theorem positionMeasure_complex_standard (n : ℕ) :
    Local.FunctionsMetaplectic.Construction.positionMeasure ℂ n complexStandardCharacter = volume := by
  simp [Local.FunctionsMetaplectic.Construction.positionMeasure, selfDualMeasure_complex_standard, volume_pi]

theorem complex_fourier_inversion_selfDual (n : ℕ)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) (x : Local.FunctionsMetaplectic.Construction.Position ℂ n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral complexStandardCharacter (Local.FunctionsMetaplectic.Construction.positionMeasure ℂ n complexStandardCharacter)
      (Local.FunctionsMetaplectic.Construction.fourierIntegral complexStandardCharacter (Local.FunctionsMetaplectic.Construction.positionMeasure ℂ n complexStandardCharacter) f.val) x =
      f.val (-x) := by
  rw [positionMeasure_complex_standard]
  exact complex_fourier_inversion_standard n f x

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ComplexFourier.LocalAnalysis
