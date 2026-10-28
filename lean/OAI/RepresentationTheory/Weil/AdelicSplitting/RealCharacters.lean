import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacters
import OAI.RepresentationTheory.Weil.AdelicSplitting.FourierTools

/-! # Real Characters -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.RealCharacters.LocalAnalysis

noncomputable section

section

/-! Real-coordinate Fourier analysis for AdelicSplitting, using the established Mathlib
Schwartz transform and the actual reference-compact Haar normalization. -/

open _root_.MeasureTheory
open scoped FourierTransform SchwartzMap NNReal

def realCharacter (c : ℝ) : AddChar ℝ ℂ :=
  Circle.coeHom.compAddChar (Real.fourierChar.mulShift c)

theorem realCharacter_apply (c t : ℝ) :
    realCharacter c t = Complex.exp (((2 * Real.pi * c * t : ℝ) : ℂ) * Complex.I) := by
  change Complex.exp (((2 * Real.pi * (c * t) : ℝ) : ℂ) * Complex.I) = _
  rw [mul_assoc (2 * Real.pi) c t]

def realReferenceHaarFactor : ℝ≥0 :=
  Measure.addHaarScalarFactor (Measure.addHaar : Measure ℝ) volume

theorem realReferenceHaarFactor_pos : 0 < realReferenceHaarFactor :=
  Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

def realSchwartzToBruhat {n : ℕ} :
    SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ n) ℂ →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n where
  toFun f := ⟨f, ArchimedeanCharacters.LocalAnalysis.schwartzBruhat_archimedean_iff.mpr ⟨f, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem realSchwartzToBruhat_bijective {n : ℕ} :
    Function.Bijective (realSchwartzToBruhat (n := n)) := by
  constructor
  · intro f g h
    exact DFunLike.ext' (congrArg Subtype.val h)
  · intro f
    obtain ⟨φ, hφ⟩ := ArchimedeanCharacters.LocalAnalysis.schwartzBruhat_archimedean_iff.mp f.property
    exact ⟨φ, Subtype.ext hφ.symm⟩

def realSchwartzEquiv (n : ℕ) :
    SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ n) ℂ ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n :=
  LinearEquiv.ofBijective realSchwartzToBruhat realSchwartzToBruhat_bijective

theorem realSchwartzEquiv_apply {n : ℕ}
    (f : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ n) ℂ) (x : Local.FunctionsMetaplectic.Construction.Position ℝ n) :
    (realSchwartzEquiv n f).val x = f x := rfl

theorem realSchwartzEquiv_symm_apply {n : ℕ}
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : Local.FunctionsMetaplectic.Construction.Position ℝ n) :
    (realSchwartzEquiv n).symm f x = f.val x := by
  have h := congrArg (fun g : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n => g.val x)
    ((realSchwartzEquiv n).apply_symm_apply f)
  exact h

def euclideanSchwartzEquiv (n : ℕ) :
    SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ n) ℂ ≃ₗ[ℂ] SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ where
  toFun f := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)) f
  invFun f := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm f
  left_inv f := by ext x; rfl
  right_inv f := by ext x; rfl
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl

def coordinateSchwartzFourier (n : ℕ) :
    SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ n) ℂ ≃ₗ[ℂ] SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ n) ℂ :=
  (euclideanSchwartzEquiv n).trans
    ((FourierTransform.fourierEquiv ℂ (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)).trans
      (euclideanSchwartzEquiv n).symm)

theorem coordinateSchwartzFourier_apply {n : ℕ}
    (f : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ n) ℂ) (x : Local.FunctionsMetaplectic.Construction.Position ℝ n) :
    coordinateSchwartzFourier n f x = Local.FunctionsMetaplectic.Construction.fourierIntegral (realCharacter 1) volume f x := by
  change 𝓕 ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)) f :
      SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)) (WithLp.toLp 2 x) = _
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 (Local.FunctionsMetaplectic.Construction.Position ℝ n)).measurableEmbedding]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    simp only [Circle.smul_def, smul_eq_mul, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial, realCharacter,
      MonoidHom.compAddChar_apply, Function.comp_apply, AddChar.mulShift_apply, one_mul]
    change (Real.fourierChar (-(∑ i, x i * y i)) : ℂ) * f y =
      f y * (Real.fourierChar (-(∑ i, x i * y i)) : ℂ)
    exact mul_comm _ _

theorem coordinateSchwartzFourier_symm_apply {n : ℕ}
    (f : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ n) ℂ) (x : Local.FunctionsMetaplectic.Construction.Position ℝ n) :
    (coordinateSchwartzFourier n).symm f x = coordinateSchwartzFourier n f (-x) := by
  change 𝓕⁻ (euclideanSchwartzEquiv n f) (WithLp.toLp 2 x) =
    𝓕 (euclideanSchwartzEquiv n f) (WithLp.toLp 2 (-x))
  rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe, Real.fourierInv_eq_fourier_neg]
  rfl

theorem coordinateSchwartzFourier_square {n : ℕ}
    (f : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ n) ℂ) (x : Local.FunctionsMetaplectic.Construction.Position ℝ n) :
    coordinateSchwartzFourier n (coordinateSchwartzFourier n f) x = f (-x) := by
  have h := congrArg (fun g : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ n) ℂ => g (-x))
    ((coordinateSchwartzFourier n).symm_apply_apply f)
  rw [coordinateSchwartzFourier_symm_apply, neg_neg] at h
  exact h

theorem coordinateSchwartzFourier_integral_norm_sq {n : ℕ}
    (f : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ n) ℂ) :
    (∫ x, ‖coordinateSchwartzFourier n f x‖ ^ 2) = ∫ x, ‖f x‖ ^ 2 := by
  have h := SchwartzMap.integral_norm_sq_fourier (euclideanSchwartzEquiv n f)
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 (Local.FunctionsMetaplectic.Construction.Position ℝ n)).measurableEmbedding,
    ← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 (Local.FunctionsMetaplectic.Construction.Position ℝ n)).measurableEmbedding] at h
  exact h

def realBruhatFourier (n : ℕ) : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n :=
  (realSchwartzEquiv n).symm.trans
    ((coordinateSchwartzFourier n).trans (realSchwartzEquiv n))

theorem realBruhatFourier_apply {n : ℕ}
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : Local.FunctionsMetaplectic.Construction.Position ℝ n) :
    (realBruhatFourier n f).val x = Local.FunctionsMetaplectic.Construction.fourierIntegral (realCharacter 1) volume f.val x := by
  change coordinateSchwartzFourier n ((realSchwartzEquiv n).symm f) x = _
  rw [coordinateSchwartzFourier_apply]
  have h : ((realSchwartzEquiv n).symm f : Local.FunctionsMetaplectic.Construction.Position ℝ n → ℂ) = f.val :=
    funext (realSchwartzEquiv_symm_apply f)
  rw [h]

theorem realBruhatFourier_square {n : ℕ}
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : Local.FunctionsMetaplectic.Construction.Position ℝ n) :
    (realBruhatFourier n (realBruhatFourier n f)).val x = f.val (-x) := by
  change coordinateSchwartzFourier n ((realSchwartzEquiv n).symm
    (realSchwartzEquiv n (coordinateSchwartzFourier n ((realSchwartzEquiv n).symm f)))) x = _
  rw [LinearEquiv.symm_apply_apply, coordinateSchwartzFourier_square,
    realSchwartzEquiv_symm_apply]

theorem real_fourier_inversion_standard {n : ℕ}
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : Local.FunctionsMetaplectic.Construction.Position ℝ n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral (realCharacter 1) volume
      (Local.FunctionsMetaplectic.Construction.fourierIntegral (realCharacter 1) volume f.val) x = f.val (-x) := by
  have h := realBruhatFourier_square f x
  rw [realBruhatFourier_apply] at h
  have hf : (realBruhatFourier n f).val = Local.FunctionsMetaplectic.Construction.fourierIntegral (realCharacter 1) volume f.val :=
    funext (realBruhatFourier_apply f)
  rwa [hf] at h

theorem real_fourier_plancherel_standard {n : ℕ}
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) :
    (∫ x, ‖Local.FunctionsMetaplectic.Construction.fourierIntegral (realCharacter 1) volume f.val x‖ ^ 2) = ∫ x, ‖f.val x‖ ^ 2 := by
  have h := coordinateSchwartzFourier_integral_norm_sq ((realSchwartzEquiv n).symm f)
  simp_rw [coordinateSchwartzFourier_apply] at h
  have hf : ((realSchwartzEquiv n).symm f : Local.FunctionsMetaplectic.Construction.Position ℝ n → ℂ) = f.val :=
    funext (realSchwartzEquiv_symm_apply f)
  simpa only [hf] using h

end

section

/-! The ordinary Fourier integral and the L² transform agree on L¹ ∩ L².
This supplies Plancherel for the reference compact set in the local oscillator definitions. -/

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

section

/-! Evaluation of the reference-set Haar normalization at a real place. -/

open _root_.MeasureTheory
open scoped FourierTransform ENNReal

theorem referenceFourier_real_standard (ξ : ℝ) :
    Local.FunctionsMetaplectic.Construction.referenceFourier ℝ (realCharacter 1) ξ =
      (realReferenceHaarFactor : ℂ) *
        𝓕 ((Local.FunctionsMetaplectic.Construction.referenceCompact ℝ : Set ℝ).indicator (fun _ : ℝ => (1 : ℂ))) ξ := by
  have hs := (Local.FunctionsMetaplectic.Construction.referenceCompact ℝ).isCompact.measurableSet
  rw [Local.FunctionsMetaplectic.Construction.referenceFourier, Measure.isAddLeftInvariant_eq_smul_of_regular
    (Measure.addHaar : Measure ℝ) volume, Measure.restrict_smul, integral_smul_nnreal_measure]
  change (realReferenceHaarFactor : ℂ) *
    (∫ x in (Local.FunctionsMetaplectic.Construction.referenceCompact ℝ : Set ℝ), realCharacter 1 (-(ξ * x))) = _
  congr 1
  rw [Real.fourier_eq, ← integral_indicator hs]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ (Local.FunctionsMetaplectic.Construction.referenceCompact ℝ : Set ℝ)
    · simp [hx, realCharacter, Circle.smul_def, mul_comm]
      rfl
    · simp [hx]

theorem real_reference_volume_pos :
    0 < volume.real (Local.FunctionsMetaplectic.Construction.referenceCompact ℝ : Set ℝ) := by
  apply ENNReal.toReal_pos
  · exact (Measure.measure_pos_of_nonempty_interior volume (Local.FunctionsMetaplectic.Construction.referenceCompact ℝ).interior_nonempty).ne'
  · exact (Local.FunctionsMetaplectic.Construction.referenceCompact ℝ).isCompact.measure_ne_top

theorem fourierHaarScaleSquared_real_standard :
    Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared ℝ (realCharacter 1) = (realReferenceHaarFactor : ℝ) ^ 2 := by
  let r : ℝ := realReferenceHaarFactor
  let s : Set ℝ := Local.FunctionsMetaplectic.Construction.referenceCompact ℝ
  have hr : r ≠ 0 := (show 0 < r from realReferenceHaarFactor_pos).ne'
  have hs : volume.real s ≠ 0 := real_reference_volume_pos.ne'
  have hhaar : (Measure.addHaar : Measure ℝ) = realReferenceHaarFactor • volume :=
    Measure.isAddLeftInvariant_eq_smul_of_regular _ _
  unfold Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared
  simp_rw [referenceFourier_real_standard, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg realReferenceHaarFactor.coe_nonneg, mul_pow]
  rw [hhaar, integral_smul_nnreal_measure, measureReal_nnreal_smul_apply]
  simp only [NNReal.smul_def, smul_eq_mul]
  rw [integral_const_mul, real_indicator_fourier_norm_sq
    (Local.FunctionsMetaplectic.Construction.referenceCompact ℝ).isCompact.measurableSet (Local.FunctionsMetaplectic.Construction.referenceCompact ℝ).isCompact.measure_ne_top]
  change (r * (r ^ 2 * volume.real s)) / (r * volume.real s) = r ^ 2
  field_simp

theorem fourierHaarScaleSquared_real_standard_pos :
    0 < Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared ℝ (realCharacter 1) := by
  rw [fourierHaarScaleSquared_real_standard]
  exact sq_pos_of_pos realReferenceHaarFactor_pos

/-- The normalization defined by a reference compact set really yields Lebesgue measure. -/
theorem selfDualMeasure_real_standard :
    Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ (realCharacter 1) = volume := by
  have hr : realReferenceHaarFactor ≠ 0 := realReferenceHaarFactor_pos.ne'
  rw [Local.FunctionsMetaplectic.Construction.selfDualMeasure, fourierHaarScaleSquared_real_standard,
    Real.sqrt_sq (by exact realReferenceHaarFactor.coe_nonneg)]
  rw [Measure.isAddLeftInvariant_eq_smul_of_regular (Measure.addHaar : Measure ℝ) volume]
  change ENNReal.ofReal ((realReferenceHaarFactor : ℝ)⁻¹) •
    (realReferenceHaarFactor • volume) = volume
  rw [← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal, ← ENNReal.smul_def,
    smul_smul, inv_mul_cancel₀ hr, one_smul]

theorem positionMeasure_real_standard (n : ℕ) :
    Local.FunctionsMetaplectic.Construction.positionMeasure ℝ n (realCharacter 1) = volume := by
  simp [Local.FunctionsMetaplectic.Construction.positionMeasure, selfDualMeasure_real_standard, volume_pi]

theorem real_fourier_inversion_selfDual {n : ℕ}
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : Local.FunctionsMetaplectic.Construction.Position ℝ n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral (realCharacter 1) (Local.FunctionsMetaplectic.Construction.positionMeasure ℝ n (realCharacter 1))
      (Local.FunctionsMetaplectic.Construction.fourierIntegral (realCharacter 1) (Local.FunctionsMetaplectic.Construction.positionMeasure ℝ n (realCharacter 1)) f.val) x =
        f.val (-x) := by
  rw [positionMeasure_real_standard]
  exact real_fourier_inversion_standard f x

theorem referenceFourier_real_shift (c ξ : ℝ) :
    Local.FunctionsMetaplectic.Construction.referenceFourier ℝ (realCharacter c) ξ =
      Local.FunctionsMetaplectic.Construction.referenceFourier ℝ (realCharacter 1) (c * ξ) := by
  unfold Local.FunctionsMetaplectic.Construction.referenceFourier
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change (Real.fourierChar (c * -(ξ * x)) : ℂ) =
      (Real.fourierChar (1 * -((c * ξ) * x)) : ℂ)
    congr 2
    ring

theorem fourierHaarScaleSquared_real (c : ℝ) :
    Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared ℝ (realCharacter c) =
      (realReferenceHaarFactor : ℝ) ^ 2 / |c| := by
  have h := Measure.integral_comp_smul (Measure.addHaar : Measure ℝ)
    (fun ξ => ‖Local.FunctionsMetaplectic.Construction.referenceFourier ℝ (realCharacter 1) ξ‖ ^ 2) c
  simp only [smul_eq_mul, Module.finrank_self, pow_one, abs_inv] at h
  calc
    _ = |c|⁻¹ * Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared ℝ (realCharacter 1) := by
      unfold Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared
      have heq : Local.FunctionsMetaplectic.Construction.referenceFourier ℝ (realCharacter c) =
          fun ξ => Local.FunctionsMetaplectic.Construction.referenceFourier ℝ (realCharacter 1) (c * ξ) :=
        funext (referenceFourier_real_shift c)
      rw [heq, h, mul_div_assoc]
    _ = _ := by rw [fourierHaarScaleSquared_real_standard]; ring

theorem fourierHaarScaleSquared_real_pos (c : ℝ) (hc : c ≠ 0) :
    0 < Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared ℝ (realCharacter c) := by
  rw [fourierHaarScaleSquared_real]
  exact div_pos (sq_pos_of_pos realReferenceHaarFactor_pos) (abs_pos.mpr hc)

theorem selfDualMeasure_real (c : ℝ) (hc : c ≠ 0) :
    Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ (realCharacter c) = ENNReal.ofReal (Real.sqrt |c|) • volume := by
  have hr : (realReferenceHaarFactor : ℝ) ≠ 0 :=
    (show (0 : ℝ) < realReferenceHaarFactor from realReferenceHaarFactor_pos).ne'
  have hs : Real.sqrt |c| ≠ 0 := (Real.sqrt_pos.mpr (abs_pos.mpr hc)).ne'
  have hscale : (Real.sqrt ((realReferenceHaarFactor : ℝ) ^ 2 / |c|))⁻¹ *
      (realReferenceHaarFactor : ℝ) = Real.sqrt |c| := by
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq realReferenceHaarFactor.coe_nonneg]
    field_simp
  rw [Local.FunctionsMetaplectic.Construction.selfDualMeasure, fourierHaarScaleSquared_real,
    Measure.isAddLeftInvariant_eq_smul_of_regular (Measure.addHaar : Measure ℝ) volume]
  change ENNReal.ofReal (Real.sqrt ((realReferenceHaarFactor : ℝ) ^ 2 / |c|))⁻¹ •
    (realReferenceHaarFactor • volume) = _
  rw [ENNReal.smul_def, smul_smul]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity), hscale]

end

section

/-! Classification of real characters from their proved derivative formula. -/

theorem real_character_eq_exp (ψ : AddChar ℝ ℂ) (hc : Continuous ψ) :
    ∃ z : ℂ, ∀ t : ℝ, ψ t = Complex.exp (z * t) := by
  obtain ⟨z, hd⟩ := ArchimedeanCharacters.LocalAnalysis.real_character_derivative ψ hc
  have hg (t : ℝ) : HasDerivAt
      (fun s : ℝ => ψ s * Complex.exp (-z * s)) 0 t := by
    have he : HasDerivAt (fun s : ℝ => Complex.exp (-z * s))
        (Complex.exp (-z * t) * -z) t :=
      by simpa using (((hasDerivAt_id t).ofReal_comp).const_mul (-z)).cexp
    have h := (hd t).mul he
    convert! h using 1
    ring
  refine ⟨z, fun t => ?_⟩
  have hconst := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt)
    (fun t => (hg t).deriv) t 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, ψ.map_zero_eq_one, mul_one] at hconst
  have he : Complex.exp (-z * (t : ℂ)) * Complex.exp (z * t) = 1 := by
    rw [← Complex.exp_add]
    ring_nf
    exact Complex.exp_zero
  calc
    ψ t = ψ t * (Complex.exp (-z * t) * Complex.exp (z * t)) := by rw [he, mul_one]
    _ = Complex.exp (z * t) := by rw [← mul_assoc, hconst, one_mul]

theorem continuous_unitary_real_character (ψ : AddChar ℝ ℂ)
    (hc : Continuous (fun t => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1) :
    ∃ c : ℝ, ψ = realCharacter c := by
  obtain ⟨z, hz⟩ := real_character_eq_exp ψ hc
  have hre : z.re = 0 := by
    have h := hu 1
    rw [hz] at h
    simpa only [Complex.ofReal_one, mul_one, Complex.norm_exp, Real.exp_eq_one_iff] using h
  refine ⟨z.im / (2 * Real.pi), ?_⟩
  ext t
  rw [hz, realCharacter_apply]
  congr 1
  have hz' : z = (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  have hr : 2 * Real.pi * (z.im / (2 * Real.pi)) * t = z.im * t := by
    field_simp
  rw [hr, Complex.ofReal_mul]
  conv_lhs => rw [hz']
  ring

theorem continuous_nontrivial_unitary_real_character (ψ : AddChar ℝ ℂ)
    (hc : Continuous (fun t => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) : ∃ c : ℝ, c ≠ 0 ∧ ψ = realCharacter c := by
  obtain ⟨c, hψ⟩ := continuous_unitary_real_character ψ hc hu
  refine ⟨c, ?_, hψ⟩
  rintro rfl
  obtain ⟨t, ht⟩ := hn
  apply ht
  rw [hψ, realCharacter_apply]
  simp

end

/-! Continuous unitary characters on a finite-dimensional real vector space
are exponentials of real linear functionals. -/

open scoped Classical

theorem continuous_unitary_vector_character
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (ψ : AddChar E ℂ) (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1) :
    ∃ L : E →ₗ[ℝ] ℝ, ∀ x, ψ x = realCharacter 1 (L x) := by
  let χ : ι → AddChar ℝ ℂ := fun i =>
    ψ.compAddMonoidHom (LinearMap.toSpanSingleton ℝ E (b i)).toAddMonoidHom
  have hχ (i : ι) : Continuous (χ i) := hc.comp (continuous_id.smul continuous_const)
  choose c h using (fun i => continuous_unitary_real_character (χ i) (hχ i) (fun t => hu (t • b i)))
  let L : E →ₗ[ℝ] ℝ := ∑ i, c i • b.coord i
  refine ⟨L, fun x => ?_⟩
  have hsum : ψ (∑ i, b.repr x i • b i) = ∏ i, ψ (b.repr x i • b i) := by
    exact map_prod ψ.toMonoidHom (fun i => Multiplicative.ofAdd (b.repr x i • b i)) Finset.univ
  rw [b.sum_repr] at hsum
  rw [hsum]
  have he (i : ι) : ψ (b.repr x i • b i) = realCharacter 1 (c i * b.repr x i) := by
    have hh := congrArg (fun χ : AddChar ℝ ℂ => χ (b.repr x i)) (h i)
    change ψ (b.repr x i • b i) = realCharacter (c i) (b.repr x i) at hh
    rw [hh]
    simp only [realCharacter_apply, mul_one, mul_assoc]
  simp_rw [he]
  have hsum' : (∏ i, realCharacter 1 (c i * b.repr x i)) =
      realCharacter 1 (∑ i, c i * b.repr x i) :=
    (map_prod (realCharacter 1).toMonoidHom
      (fun i => Multiplicative.ofAdd (c i * b.repr x i)) Finset.univ).symm
  rw [hsum']
  congr 1
  simp [L, LinearMap.sum_apply, Module.Basis.coord_apply]

theorem realCharacter_one_eq_one_iff (t : ℝ) :
    realCharacter 1 t = 1 ↔ ∃ z : ℤ, (z : ℝ) = t := by
  rw [realCharacter_apply, mul_one, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨z, hz⟩
    have hi := congrArg Complex.im hz
    have he : (2 * Real.pi) * t = (2 * Real.pi) * (z : ℝ) := by
      simpa [Complex.mul_im, mul_assoc, mul_comm, mul_left_comm] using hi
    exact ⟨z, (mul_left_cancel₀ (by positivity : 2 * Real.pi ≠ 0) he).symm⟩
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    push_cast
    ring

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.RealCharacters.LocalAnalysis
