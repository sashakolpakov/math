import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic

/-! # Gaussian -/

namespace OAI.RepresentationTheory.Weil.Local.Gaussian.Construction

noncomputable section

/-! Checks of the Gaussian construction against the real Gaussian integral. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology NNReal

theorem phase_positive_mul (r : ℝ) (hr : 0 < r) (z : ℂ) :
    FunctionsMetaplectic.Construction.phase ((r : ℂ) * z) = FunctionsMetaplectic.Construction.phase z := by
  simp only [FunctionsMetaplectic.Construction.phase, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr, Complex.ofReal_mul]
  exact mul_div_mul_left z (‖z‖ : ℂ) (Complex.ofReal_ne_zero.mpr hr.ne')

theorem phase_pow (z : ℂ) (n : ℕ) : FunctionsMetaplectic.Construction.phase z ^ n = FunctionsMetaplectic.Construction.phase (z ^ n) := by
  simp only [FunctionsMetaplectic.Construction.phase, div_pow, norm_pow, Complex.ofReal_pow]

theorem phase_positive_real (r : ℝ) (hr : 0 < r) : FunctionsMetaplectic.Construction.phase (r : ℂ) = 1 := by
  simp [FunctionsMetaplectic.Construction.phase, Complex.norm_real, abs_of_pos hr, hr.ne']

/-- ψ_c(t) = exp(2π i c t), with the manuscript's sign convention. -/
def realCharacter (c : ℝ) : AddChar ℝ ℂ :=
  Circle.coeHom.compAddChar (Real.fourierChar.mulShift c)

theorem realCharacter_apply (c t : ℝ) :
    realCharacter c t = Complex.exp (((2 * Real.pi * c * t : ℝ) : ℂ) * Complex.I) := by
  change Complex.exp (((2 * Real.pi * (c * t) : ℝ) : ℂ) * Complex.I) = _
  rw [mul_assoc (2 * Real.pi) c t]

def realDampedGaussian (c a ε : ℝ) : ℂ :=
  ∫ x : ℝ, (Real.exp (-ε * ‖x‖ ^ 2) : ℂ) * realCharacter c (a * x ^ 2 / 2)

/-- Actual evaluation of the damped oscillatory integral, not a
postulated value of a Weil-index symbol. -/
theorem realDampedGaussian_eq (c a ε : ℝ) (hε : 0 < ε) :
    realDampedGaussian c a ε =
      ((Real.pi : ℂ) / ((ε : ℂ) - Real.pi * c * a * Complex.I)) ^ (1 / 2 : ℂ) := by
  have hfun : (fun x : ℝ =>
      (Real.exp (-ε * ‖x‖ ^ 2) : ℂ) * realCharacter c (a * x ^ 2 / 2)) =
      (fun x : ℝ => Complex.exp
        (-((ε : ℂ) - Real.pi * c * a * Complex.I) * (x : ℂ) ^ 2)) := by
    funext x
    rw [realCharacter_apply, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    simp only [Real.norm_eq_abs, sq_abs]
    push_cast
    ring
  rw [realDampedGaussian, hfun]
  exact integral_gaussian_complex (by simpa using hε)

def realReferenceHaarFactor : ℝ≥0 :=
  Measure.addHaarScalarFactor (Measure.addHaar : Measure ℝ) volume

theorem realReferenceHaarFactor_pos : 0 < realReferenceHaarFactor :=
  Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

theorem regularizedGaussian_real (c a ε : ℝ) :
    FunctionsMetaplectic.Construction.regularizedGaussian ℝ (realCharacter c) a ε =
      (realReferenceHaarFactor : ℂ) * realDampedGaussian c a ε := by
  unfold FunctionsMetaplectic.Construction.regularizedGaussian realDampedGaussian
  rw [Measure.isAddLeftInvariant_eq_smul_of_regular
    (Measure.addHaar : Measure ℝ) volume]
  simp only [integral_smul_nnreal_measure, realReferenceHaarFactor,
    NNReal.smul_def, Complex.real_smul]

theorem regularizedGaussian_real_eq (c a ε : ℝ) (hε : 0 < ε) :
    FunctionsMetaplectic.Construction.regularizedGaussian ℝ (realCharacter c) a ε =
      (realReferenceHaarFactor : ℂ) *
        (((Real.pi : ℂ) / ((ε : ℂ) - Real.pi * c * a * Complex.I)) ^ (1 / 2 : ℂ)) := by
  rw [regularizedGaussian_real, realDampedGaussian_eq c a ε hε]

theorem realGaussian_ratio_at_zero (c a : ℝ) (hc : c ≠ 0) (ha : a ≠ 0) :
    (Real.pi : ℂ) / ((0 : ℂ) - Real.pi * c * a * Complex.I) =
      Complex.I / ((c : ℂ) * a) := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  linear_combination (Real.pi : ℂ) * c * a * Complex.I_sq

theorem regularizedGaussian_real_tendsto (c a : ℝ) (hc : c ≠ 0) (ha : a ≠ 0) :
    Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian ℝ (realCharacter c) a) (𝓝[>] (0 : ℝ))
      (𝓝 ((realReferenceHaarFactor : ℂ) *
        (Complex.I / ((c : ℂ) * a)) ^ (1 / 2 : ℂ))) := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hden : (0 : ℂ) - Real.pi * c * a * Complex.I ≠ 0 := by
    simp [hc', ha', Real.pi_ne_zero]
  have hbase : ContinuousAt (fun ε : ℝ =>
      (Real.pi : ℂ) / ((ε : ℂ) - Real.pi * c * a * Complex.I)) 0 :=
    continuousAt_const.div (Complex.continuous_ofReal.continuousAt.sub continuousAt_const) hden
  have hslit : Complex.I / ((c : ℂ) * a) ∈ Complex.slitPlane := by
    apply Or.inr
    simp [Complex.div_im, hc, ha]
  have hr : (Real.pi : ℂ) / (((0 : ℝ) : ℂ) - Real.pi * c * a * Complex.I) =
      Complex.I / ((c : ℂ) * a) := by
    simpa using realGaussian_ratio_at_zero c a hc ha
  have hlimit : Tendsto (fun ε : ℝ => (realReferenceHaarFactor : ℂ) *
      ((Real.pi : ℂ) / ((ε : ℂ) - Real.pi * c * a * Complex.I)) ^ (1 / 2 : ℂ))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((realReferenceHaarFactor : ℂ) *
        ((Real.pi : ℂ) / (((0 : ℝ) : ℂ) - Real.pi * c * a * Complex.I)) ^ (1 / 2 : ℂ))) :=
    ((hbase.tendsto.mono_left nhdsWithin_le_nhds).cpow
      tendsto_const_nhds (by rwa [hr])).const_mul (realReferenceHaarFactor : ℂ)
  rw [hr] at hlimit
  apply hlimit.congr'
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with ε hε
  exact (regularizedGaussian_real_eq c a ε hε).symm

theorem gaussianIntegral_real_eq (c a : ℝ) (hc : c ≠ 0) (ha : a ≠ 0) :
    FunctionsMetaplectic.Construction.gaussianIntegral ℝ (realCharacter c) a =
      (realReferenceHaarFactor : ℂ) *
        (Complex.I / ((c : ℂ) * a)) ^ (1 / 2 : ℂ) :=
  (regularizedGaussian_real_tendsto c a hc ha).limUnder_eq

theorem gaussianIntegral_real_ne_zero (c a : ℝ) (hc : c ≠ 0) (ha : a ≠ 0) :
    FunctionsMetaplectic.Construction.gaussianIntegral ℝ (realCharacter c) a ≠ 0 := by
  rw [gaussianIntegral_real_eq c a hc ha]
  apply mul_ne_zero
  · exact_mod_cast realReferenceHaarFactor_pos.ne'
  · apply Complex.cpow_ne_zero_iff.mpr
    exact Or.inl (div_ne_zero Complex.I_ne_zero
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr hc) (Complex.ofReal_ne_zero.mpr ha)))

/-- The general oscillatory definition specializes to the usual real
Gaussian phase, with the arbitrary reference Haar scale canceled. -/
theorem gaussianIndex_real_eq (c a : ℝ) (hc : c ≠ 0) (ha : a ≠ 0) :
    FunctionsMetaplectic.Construction.gaussianIndex ℝ (realCharacter c) a =
      FunctionsMetaplectic.Construction.phase ((Complex.I / ((c : ℂ) * a)) ^ (1 / 2 : ℂ)) := by
  rw [FunctionsMetaplectic.Construction.gaussianIndex, gaussianIntegral_real_eq c a hc ha]
  exact phase_positive_mul _ realReferenceHaarFactor_pos _

theorem gaussianIndex_real_norm (c a : ℝ) (hc : c ≠ 0) (ha : a ≠ 0) :
    ‖FunctionsMetaplectic.Construction.gaussianIndex ℝ (realCharacter c) a‖ = 1 :=
  FunctionsMetaplectic.Construction.gaussianIndex_norm ℝ (realCharacter c) a (gaussianIntegral_real_ne_zero c a hc ha)

/-- The local root-of-unity assertion is already proved at real places. -/
theorem gaussianIndex_real_eighth_power (c a : ℝ) (hc : c ≠ 0) (ha : a ≠ 0) :
    FunctionsMetaplectic.Construction.gaussianIndex ℝ (realCharacter c) a ^ 8 = 1 := by
  rw [gaussianIndex_real_eq c a hc ha, phase_pow]
  have hsquare : ((Complex.I / ((c : ℂ) * a)) ^ (1 / 2 : ℂ)) ^ (2 : ℕ) =
      Complex.I / ((c : ℂ) * a) := by
    simp [one_div]
  have heighth : ((Complex.I / ((c : ℂ) * a)) ^ (1 / 2 : ℂ)) ^ (8 : ℕ) =
      (((c * a) ^ 4)⁻¹ : ℝ) := by
    calc
      _ = (((Complex.I / ((c : ℂ) * a)) ^ (1 / 2 : ℂ)) ^ (2 : ℕ)) ^ (4 : ℕ) := by
        rw [← pow_mul]
      _ = (Complex.I / ((c : ℂ) * a)) ^ (4 : ℕ) := by rw [hsquare]
      _ = (((c * a) ^ 4)⁻¹ : ℝ) := by
        rw [div_pow]
        norm_num
  rw [heighth]
  apply phase_positive_real
  have hca : c * a ≠ 0 := mul_ne_zero hc ha
  positivity

end

end OAI.RepresentationTheory.Weil.Local.Gaussian.Construction
