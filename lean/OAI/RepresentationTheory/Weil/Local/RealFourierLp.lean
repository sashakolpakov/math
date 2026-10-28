import OAI.RepresentationTheory.Weil.Local.RealTestSpace
import OAI.RepresentationTheory.Weil.Local.FourierTools

/-! # Real Fourier Lp -/

namespace OAI.RepresentationTheory.Weil.Local.RealFourierLp.Construction

noncomputable section

section

/-! Fourier inversion and Plancherel on the real coordinate test space. -/

open _root_.MeasureTheory
open scoped FourierTransform SchwartzMap

def euclideanSchwartzEquiv (n : ℕ) :
    SchwartzMap (FunctionsMetaplectic.Construction.Position ℝ n) ℂ ≃ₗ[ℂ] SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ where
  toFun f := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)) f
  invFun f := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm f
  left_inv f := by ext x; rfl
  right_inv f := by ext x; rfl
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl

def coordinateSchwartzFourier (n : ℕ) :
    SchwartzMap (FunctionsMetaplectic.Construction.Position ℝ n) ℂ ≃ₗ[ℂ] SchwartzMap (FunctionsMetaplectic.Construction.Position ℝ n) ℂ :=
  (euclideanSchwartzEquiv n).trans
    ((FourierTransform.fourierEquiv ℂ (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)).trans
      (euclideanSchwartzEquiv n).symm)

theorem coordinateSchwartzFourier_apply {n : ℕ}
    (f : SchwartzMap (FunctionsMetaplectic.Construction.Position ℝ n) ℂ) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    coordinateSchwartzFourier n f x = FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter 1) volume f x := by
  change 𝓕 ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)) f :
      SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)) (WithLp.toLp 2 x) = _
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 (FunctionsMetaplectic.Construction.Position ℝ n)).measurableEmbedding]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    simp only [Circle.smul_def, smul_eq_mul, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial, Gaussian.Construction.realCharacter,
      MonoidHom.compAddChar_apply, Function.comp_apply, AddChar.mulShift_apply, one_mul]
    change (Real.fourierChar (-(∑ i, x i * y i)) : ℂ) * f y =
      f y * (Real.fourierChar (-(∑ i, x i * y i)) : ℂ)
    exact mul_comm _ _

theorem coordinateSchwartzFourier_symm_apply {n : ℕ}
    (f : SchwartzMap (FunctionsMetaplectic.Construction.Position ℝ n) ℂ) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    (coordinateSchwartzFourier n).symm f x = coordinateSchwartzFourier n f (-x) := by
  change 𝓕⁻ (euclideanSchwartzEquiv n f) (WithLp.toLp 2 x) =
    𝓕 (euclideanSchwartzEquiv n f) (WithLp.toLp 2 (-x))
  rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe, Real.fourierInv_eq_fourier_neg]
  rfl

theorem coordinateSchwartzFourier_square {n : ℕ}
    (f : SchwartzMap (FunctionsMetaplectic.Construction.Position ℝ n) ℂ) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    coordinateSchwartzFourier n (coordinateSchwartzFourier n f) x = f (-x) := by
  have h := congrArg (fun g : SchwartzMap (FunctionsMetaplectic.Construction.Position ℝ n) ℂ => g (-x))
    ((coordinateSchwartzFourier n).symm_apply_apply f)
  rw [coordinateSchwartzFourier_symm_apply, neg_neg] at h
  exact h

theorem coordinateSchwartzFourier_integral_norm_sq {n : ℕ}
    (f : SchwartzMap (FunctionsMetaplectic.Construction.Position ℝ n) ℂ) :
    (∫ x, ‖coordinateSchwartzFourier n f x‖ ^ 2) = ∫ x, ‖f x‖ ^ 2 := by
  have h := SchwartzMap.integral_norm_sq_fourier (euclideanSchwartzEquiv n f)
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 (FunctionsMetaplectic.Construction.Position ℝ n)).measurableEmbedding,
    ← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 (FunctionsMetaplectic.Construction.Position ℝ n)).measurableEmbedding] at h
  exact h

def realBruhatFourier (n : ℕ) : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n ≃ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat ℝ n :=
  (RealTestSpace.Construction.realSchwartzEquiv n).symm.trans
    ((coordinateSchwartzFourier n).trans (RealTestSpace.Construction.realSchwartzEquiv n))

theorem realBruhatFourier_apply {n : ℕ}
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    (realBruhatFourier n f).val x = FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter 1) volume f.val x := by
  change coordinateSchwartzFourier n ((RealTestSpace.Construction.realSchwartzEquiv n).symm f) x = _
  rw [coordinateSchwartzFourier_apply]
  have h : ((RealTestSpace.Construction.realSchwartzEquiv n).symm f : FunctionsMetaplectic.Construction.Position ℝ n → ℂ) = f.val :=
    funext (RealTestSpace.Construction.realSchwartzEquiv_symm_apply f)
  rw [h]

theorem realBruhatFourier_square {n : ℕ}
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    (realBruhatFourier n (realBruhatFourier n f)).val x = f.val (-x) := by
  change coordinateSchwartzFourier n ((RealTestSpace.Construction.realSchwartzEquiv n).symm
    (RealTestSpace.Construction.realSchwartzEquiv n (coordinateSchwartzFourier n ((RealTestSpace.Construction.realSchwartzEquiv n).symm f)))) x = _
  rw [LinearEquiv.symm_apply_apply, coordinateSchwartzFourier_square,
    RealTestSpace.Construction.realSchwartzEquiv_symm_apply]

theorem real_fourier_inversion_standard {n : ℕ}
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter 1) volume
      (FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter 1) volume f.val) x = f.val (-x) := by
  have h := realBruhatFourier_square f x
  rw [realBruhatFourier_apply] at h
  have hf : (realBruhatFourier n f).val = FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter 1) volume f.val :=
    funext (realBruhatFourier_apply f)
  rwa [hf] at h

theorem real_fourier_plancherel_standard {n : ℕ}
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) :
    (∫ x, ‖FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter 1) volume f.val x‖ ^ 2) = ∫ x, ‖f.val x‖ ^ 2 := by
  have h := coordinateSchwartzFourier_integral_norm_sq ((RealTestSpace.Construction.realSchwartzEquiv n).symm f)
  simp_rw [coordinateSchwartzFourier_apply] at h
  have hf : ((RealTestSpace.Construction.realSchwartzEquiv n).symm f : FunctionsMetaplectic.Construction.Position ℝ n → ℂ) = f.val :=
    funext (RealTestSpace.Construction.realSchwartzEquiv_symm_apply f)
  simpa only [hf] using h

end

section

/-! The ordinary Fourier integral and the L² transform agree on L¹ ∩ L².
This supplies Plancherel for the reference compact set used in LocalWeil. -/

open _root_.MeasureTheory FourierTransform
open scoped FourierTransform SchwartzMap ContDiff ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem integral_fourier_mul_swap {f g : E → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ x, 𝓕 f x * g x) = ∫ x, f x * 𝓕 g x := by
  simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ E)
    Real.continuous_fourierChar continuous_inner hf hg

theorem fourier_integral_ae_L2 {f : E → ℂ}
    (hf : Integrable f) (hf₂ : MemLp f 2) :
    𝓕 f =ᵐ[volume] (𝓕 (hf₂.toLp f) : Lp ℂ 2 (volume : Measure E)) := by
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf
  apply ae_eq_of_integral_contDiff_smul_eq hcont.locallyIntegrable
    ((Lp.memLp (𝓕 (hf₂.toLp f))).locallyIntegrable (by norm_num))
  intro g hg hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let φ : SchwartzMap E ℂ := hc'.toSchwartzMap hg'
  have hdist := congrArg (fun T : TemperedDistribution E ℂ => T φ)
    (Lp.fourier_toTemperedDistribution_eq (hf₂.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
    smul_eq_mul] at hdist
  have hpair : (∫ x, 𝓕 φ x * f x) = ∫ x, φ x * (𝓕 (hf₂.toLp f) : Lp ℂ 2 (volume : Measure E)) x := by
    calc
      _ = ∫ x, 𝓕 φ x * (hf₂.toLp f) x := by
        apply integral_congr_ae
        filter_upwards [hf₂.coeFn_toLp] with x hx
        rw [hx]
      _ = _ := hdist
  calc
    _ = ∫ x, 𝓕 f x * φ x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change g x • 𝓕 f x = 𝓕 f x * (g x : ℂ)
        rw [Complex.real_smul, mul_comm]
    _ = ∫ x, f x * 𝓕 φ x := by
      exact integral_fourier_mul_swap hf φ.integrable
    _ = ∫ x, φ x * (𝓕 (hf₂.toLp f) : Lp ℂ 2 (volume : Measure E)) x := by
      rw [← hpair]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change (g x : ℂ) * _ = g x • _
        rw [Complex.real_smul]

theorem memLp_fourier_integral {f : E → ℂ} (hf : Integrable f) (hf₂ : MemLp f 2) :
    MemLp (𝓕 f) 2 :=
  (memLp_congr_ae (fourier_integral_ae_L2 hf hf₂)).mpr (Lp.memLp _)

theorem L2_integral_norm_sq (f : Lp ℂ 2 (volume : Measure E)) :
    (∫ x, ‖f x‖ ^ 2) = ‖f‖ ^ 2 := by
  rw [Lp.norm_def, toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      (Lp.aestronglyMeasurable f)]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two, invOf_eq_inv]
  rw [← Real.sqrt_eq_rpow]
  exact (Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg ‖f x‖))).symm

theorem real_integral_fourier_norm_sq {f : E → ℂ}
    (hf : Integrable f) (hf₂ : MemLp f 2) :
    (∫ x, ‖𝓕 f x‖ ^ 2) = ∫ x, ‖f x‖ ^ 2 := by
  calc
    _ = ∫ x, ‖(𝓕 (hf₂.toLp f) : Lp ℂ 2 (volume : Measure E)) x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [fourier_integral_ae_L2 hf hf₂] with x hx
      rw [hx]
    _ = ‖(𝓕 (hf₂.toLp f) : Lp ℂ 2 (volume : Measure E))‖ ^ 2 := L2_integral_norm_sq _
    _ = ‖hf₂.toLp f‖ ^ 2 := by rw [Lp.norm_fourier_eq]
    _ = ∫ x, ‖(hf₂.toLp f) x‖ ^ 2 := (L2_integral_norm_sq _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf₂.coeFn_toLp] with x hx
      rw [hx]

theorem real_indicator_fourier_norm_sq {s : Set E} (hs : MeasurableSet s)
    (hfin : volume s ≠ ⊤) :
    (∫ x, ‖𝓕 (s.indicator (fun _ : E => (1 : ℂ))) x‖ ^ 2) = volume.real s := by
  have hf (p : ℝ≥0∞) : MemLp (s.indicator (fun _ : E => (1 : ℂ))) p :=
    memLp_indicator_const p hs 1 (Or.inr hfin)
  rw [real_integral_fourier_norm_sq (memLp_one_iff_integrable.mp (hf 1)) (hf 2)]
  have heq : (fun x => ‖s.indicator (fun _ : E => (1 : ℂ)) x‖ ^ 2) =
      s.indicator (fun _ : E => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [heq]
  exact integral_indicator_one hs

end

/-! Evaluation of the reference-set Haar normalization at a real place. -/

open _root_.MeasureTheory
open scoped FourierTransform ENNReal

theorem referenceFourier_real_standard (ξ : ℝ) :
    FunctionsMetaplectic.Construction.referenceFourier ℝ (Gaussian.Construction.realCharacter 1) ξ =
      (Gaussian.Construction.realReferenceHaarFactor : ℂ) *
        𝓕 ((FunctionsMetaplectic.Construction.referenceCompact ℝ : Set ℝ).indicator (fun _ : ℝ => (1 : ℂ))) ξ := by
  have hs := (FunctionsMetaplectic.Construction.referenceCompact ℝ).isCompact.measurableSet
  rw [FunctionsMetaplectic.Construction.referenceFourier, Measure.isAddLeftInvariant_eq_smul_of_regular
    (Measure.addHaar : Measure ℝ) volume, Measure.restrict_smul, integral_smul_nnreal_measure]
  change (Gaussian.Construction.realReferenceHaarFactor : ℂ) *
    (∫ x in (FunctionsMetaplectic.Construction.referenceCompact ℝ : Set ℝ), Gaussian.Construction.realCharacter 1 (-(ξ * x))) = _
  congr 1
  rw [Real.fourier_eq, ← integral_indicator hs]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ (FunctionsMetaplectic.Construction.referenceCompact ℝ : Set ℝ)
    · simp [hx, Gaussian.Construction.realCharacter, Circle.smul_def, mul_comm]
      rfl
    · simp [hx]

theorem real_reference_volume_pos :
    0 < volume.real (FunctionsMetaplectic.Construction.referenceCompact ℝ : Set ℝ) := by
  apply ENNReal.toReal_pos
  · exact (Measure.measure_pos_of_nonempty_interior volume (FunctionsMetaplectic.Construction.referenceCompact ℝ).interior_nonempty).ne'
  · exact (FunctionsMetaplectic.Construction.referenceCompact ℝ).isCompact.measure_ne_top

theorem fourierHaarScaleSquared_real_standard :
    FunctionsMetaplectic.Construction.fourierHaarScaleSquared ℝ (Gaussian.Construction.realCharacter 1) = (Gaussian.Construction.realReferenceHaarFactor : ℝ) ^ 2 := by
  let r : ℝ := Gaussian.Construction.realReferenceHaarFactor
  let s : Set ℝ := FunctionsMetaplectic.Construction.referenceCompact ℝ
  have hr : r ≠ 0 := (show 0 < r from Gaussian.Construction.realReferenceHaarFactor_pos).ne'
  have hs : volume.real s ≠ 0 := real_reference_volume_pos.ne'
  have hhaar : (Measure.addHaar : Measure ℝ) = Gaussian.Construction.realReferenceHaarFactor • volume :=
    Measure.isAddLeftInvariant_eq_smul_of_regular _ _
  unfold FunctionsMetaplectic.Construction.fourierHaarScaleSquared
  simp_rw [referenceFourier_real_standard, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg Gaussian.Construction.realReferenceHaarFactor.coe_nonneg, mul_pow]
  rw [hhaar, integral_smul_nnreal_measure, measureReal_nnreal_smul_apply]
  simp only [NNReal.smul_def, smul_eq_mul]
  rw [integral_const_mul, real_indicator_fourier_norm_sq
    (FunctionsMetaplectic.Construction.referenceCompact ℝ).isCompact.measurableSet (FunctionsMetaplectic.Construction.referenceCompact ℝ).isCompact.measure_ne_top]
  change (r * (r ^ 2 * volume.real s)) / (r * volume.real s) = r ^ 2
  field_simp

theorem fourierHaarScaleSquared_real_standard_pos :
    0 < FunctionsMetaplectic.Construction.fourierHaarScaleSquared ℝ (Gaussian.Construction.realCharacter 1) := by
  rw [fourierHaarScaleSquared_real_standard]
  exact sq_pos_of_pos Gaussian.Construction.realReferenceHaarFactor_pos

/-- The normalization defined by a reference compact set really yields Lebesgue measure. -/
theorem selfDualMeasure_real_standard :
    FunctionsMetaplectic.Construction.selfDualMeasure ℝ (Gaussian.Construction.realCharacter 1) = volume := by
  have hr : Gaussian.Construction.realReferenceHaarFactor ≠ 0 := Gaussian.Construction.realReferenceHaarFactor_pos.ne'
  rw [FunctionsMetaplectic.Construction.selfDualMeasure, fourierHaarScaleSquared_real_standard,
    Real.sqrt_sq (by exact Gaussian.Construction.realReferenceHaarFactor.coe_nonneg)]
  rw [Measure.isAddLeftInvariant_eq_smul_of_regular (Measure.addHaar : Measure ℝ) volume]
  change ENNReal.ofReal ((Gaussian.Construction.realReferenceHaarFactor : ℝ)⁻¹) •
    (Gaussian.Construction.realReferenceHaarFactor • volume) = volume
  rw [← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal, ← ENNReal.smul_def,
    smul_smul, inv_mul_cancel₀ hr, one_smul]

theorem positionMeasure_real_standard (n : ℕ) :
    FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter 1) = volume := by
  simp [FunctionsMetaplectic.Construction.positionMeasure, selfDualMeasure_real_standard, volume_pi]

theorem real_fourier_inversion_selfDual {n : ℕ}
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter 1) (FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter 1))
      (FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter 1) (FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter 1)) f.val) x =
        f.val (-x) := by
  rw [positionMeasure_real_standard]
  exact real_fourier_inversion_standard f x

theorem referenceFourier_real_shift (c ξ : ℝ) :
    FunctionsMetaplectic.Construction.referenceFourier ℝ (Gaussian.Construction.realCharacter c) ξ =
      FunctionsMetaplectic.Construction.referenceFourier ℝ (Gaussian.Construction.realCharacter 1) (c * ξ) := by
  unfold FunctionsMetaplectic.Construction.referenceFourier
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change (Real.fourierChar (c * -(ξ * x)) : ℂ) =
      (Real.fourierChar (1 * -((c * ξ) * x)) : ℂ)
    congr 2
    ring

theorem fourierHaarScaleSquared_real (c : ℝ) :
    FunctionsMetaplectic.Construction.fourierHaarScaleSquared ℝ (Gaussian.Construction.realCharacter c) =
      (Gaussian.Construction.realReferenceHaarFactor : ℝ) ^ 2 / |c| := by
  have h := Measure.integral_comp_smul (Measure.addHaar : Measure ℝ)
    (fun ξ => ‖FunctionsMetaplectic.Construction.referenceFourier ℝ (Gaussian.Construction.realCharacter 1) ξ‖ ^ 2) c
  simp only [smul_eq_mul, Module.finrank_self, pow_one, abs_inv] at h
  calc
    _ = |c|⁻¹ * FunctionsMetaplectic.Construction.fourierHaarScaleSquared ℝ (Gaussian.Construction.realCharacter 1) := by
      unfold FunctionsMetaplectic.Construction.fourierHaarScaleSquared
      have heq : FunctionsMetaplectic.Construction.referenceFourier ℝ (Gaussian.Construction.realCharacter c) =
          fun ξ => FunctionsMetaplectic.Construction.referenceFourier ℝ (Gaussian.Construction.realCharacter 1) (c * ξ) :=
        funext (referenceFourier_real_shift c)
      rw [heq, h, mul_div_assoc]
    _ = _ := by rw [fourierHaarScaleSquared_real_standard]; ring

theorem fourierHaarScaleSquared_real_pos (c : ℝ) (hc : c ≠ 0) :
    0 < FunctionsMetaplectic.Construction.fourierHaarScaleSquared ℝ (Gaussian.Construction.realCharacter c) := by
  rw [fourierHaarScaleSquared_real]
  exact div_pos (sq_pos_of_pos Gaussian.Construction.realReferenceHaarFactor_pos) (abs_pos.mpr hc)

theorem selfDualMeasure_real (c : ℝ) (hc : c ≠ 0) :
    FunctionsMetaplectic.Construction.selfDualMeasure ℝ (Gaussian.Construction.realCharacter c) = ENNReal.ofReal (Real.sqrt |c|) • volume := by
  have hr : (Gaussian.Construction.realReferenceHaarFactor : ℝ) ≠ 0 :=
    (show (0 : ℝ) < Gaussian.Construction.realReferenceHaarFactor from Gaussian.Construction.realReferenceHaarFactor_pos).ne'
  have hs : Real.sqrt |c| ≠ 0 := (Real.sqrt_pos.mpr (abs_pos.mpr hc)).ne'
  have hscale : (Real.sqrt ((Gaussian.Construction.realReferenceHaarFactor : ℝ) ^ 2 / |c|))⁻¹ *
      (Gaussian.Construction.realReferenceHaarFactor : ℝ) = Real.sqrt |c| := by
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq Gaussian.Construction.realReferenceHaarFactor.coe_nonneg]
    field_simp
  rw [FunctionsMetaplectic.Construction.selfDualMeasure, fourierHaarScaleSquared_real,
    Measure.isAddLeftInvariant_eq_smul_of_regular (Measure.addHaar : Measure ℝ) volume]
  change ENNReal.ofReal (Real.sqrt ((Gaussian.Construction.realReferenceHaarFactor : ℝ) ^ 2 / |c|))⁻¹ •
    (Gaussian.Construction.realReferenceHaarFactor • volume) = _
  rw [ENNReal.smul_def, smul_smul]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity), hscale]

end

end OAI.RepresentationTheory.Weil.Local.RealFourierLp.Construction
