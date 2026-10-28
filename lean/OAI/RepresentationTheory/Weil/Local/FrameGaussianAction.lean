import OAI.RepresentationTheory.Weil.Local.FrameGenerators
import OAI.RepresentationTheory.Weil.Local.RealGenerators

/-! # Frame Gaussian Action -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Weil.Local

/-! Actual Gaussian vectors and the prescribed real bare generator actions. -/

open _root_.Matrix _root_.MeasureTheory

theorem SiegelGaussian.Construction.PositiveLagrangianFrame.gaussian_memLp {n : ℕ} (P : SiegelGaussian.Construction.PositiveLagrangianFrame n) :
    MemLp (SiegelGaussian.Construction.siegelGaussian P.quadraticMatrix) 2 (UnitaryInner.Construction.referencePositionMeasure ℝ n) :=
  RealGenerators.Construction.real_memLp_reference_of_volume (SiegelGaussian.Construction.siegelGaussian_memLp_two _
    P.quadraticMatrix_symmetric P.imaginaryPart_positive)

def SiegelGaussian.Construction.PositiveLagrangianFrame.gaussianLp {n : ℕ} (P : SiegelGaussian.Construction.PositiveLagrangianFrame n) :
    Lp ℂ 2 (UnitaryInner.Construction.referencePositionMeasure ℝ n) :=
  P.gaussian_memLp.toLp (SiegelGaussian.Construction.siegelGaussian P.quadraticMatrix)

theorem SiegelGaussian.Construction.PositiveLagrangianFrame.gaussianLp_ne_zero {n : ℕ} (P : SiegelGaussian.Construction.PositiveLagrangianFrame n) :
    P.gaussianLp ≠ 0 := by
  intro h
  have he : SiegelGaussian.Construction.siegelGaussian P.quadraticMatrix =ᵐ[UnitaryInner.Construction.referencePositionMeasure ℝ n] 0 :=
    (MemLp.toLp_eq_toLp_iff P.gaussian_memLp MemLp.zero).mp h
  have hf := Measure.eq_of_ae_eq he (SiegelGaussian.Construction.siegelGaussian_continuous _) continuous_const
  have hz := congrFun hf 0
  exact one_ne_zero (by simpa only [SiegelGaussian.Construction.siegelGaussian_zero, Pi.zero_apply] using hz)

theorem SiegelGaussian.Construction.PositiveLagrangianFrame.lower_gaussianLp {n : ℕ} (P : SiegelGaussian.Construction.PositiveLagrangianFrame n)
    (B : FunctionsMetaplectic.Construction.SymmetricMatrix ℝ n) :
    RealOscillator.Construction.realL2Oscillator n (Gaussian.Construction.realCharacter 1) (QuadraticIntertwiner.Construction.realQuadraticMetaplectic 1 B).val P.gaussianLp =
      (P.act (Generators.Construction.quadraticSymplectic B)).gaussianLp := by
  apply RealGenerators.Construction.realL2Oscillator_multiplier (Gaussian.Construction.realCharacter 1) _
    (fun x => Gaussian.Construction.realCharacter 1 (FunctionsMetaplectic.Construction.quadratic B.val x))
    (fun x => QuadraticIntertwiner.Construction.realCharacter_unitary 1 _) (QuadraticIntertwiner.Construction.realQuadraticMetaplectic_apply 1 B)
  intro x
  rw [P.lower_quadraticMatrix]
  exact (FrameGenerators.Construction.siegelGaussian_quadratic_mul _ B.val x).symm

theorem SiegelGaussian.Construction.PositiveLagrangianFrame.fourier_gaussianLp {n : ℕ} (P : SiegelGaussian.Construction.PositiveLagrangianFrame n) :
    ∃ c : ℂ, c ^ 2 * P.quadraticMatrix.det = Complex.I ^ n ∧
      RealOscillator.Construction.realL2Oscillator n (Gaussian.Construction.realCharacter 1) (RealFourierFamily.Construction.realFourierOscillatorFamily n 1 one_ne_zero) P.gaussianLp =
        c • (P.act (Generators.Construction.weylSymplectic ℝ n)).gaussianLp := by
  obtain ⟨c, hc, hF⟩ := SiegelGaussian.Construction.siegelGaussian_fourier P.quadraticMatrix
    P.quadraticMatrix_symmetric P.imaginaryPart_positive
  refine ⟨c, hc, ?_⟩
  exact RealGenerators.Construction.realL2Oscillator_fourier
    (SiegelGaussian.Construction.siegelGaussian_integrable _ P.quadraticMatrix_symmetric P.imaginaryPart_positive)
    P.gaussian_memLp ((P.act (Generators.Construction.weylSymplectic ℝ n)).gaussian_memLp.const_smul c)
    (fun x => by
      change c * SiegelGaussian.Construction.siegelGaussian (P.act (Generators.Construction.weylSymplectic ℝ n)).quadraticMatrix x = _
      rw [P.weyl_quadraticMatrix]
      exact (hF x).symm)

theorem FrameGaussianAction.Construction.real_standard_gaussianIndex_square :
    FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter 1) 1 ^ 2 = Complex.I := by
  have h := RealFresnelNormalization.Construction.realGaussian_coefficient_normalized 1 one_ne_zero
  simp only [abs_one, Real.sqrt_one, Complex.ofReal_one, one_mul, div_one] at h
  rw [← h]
  simp [one_div]

theorem SiegelGaussian.Construction.PositiveLagrangianFrame.bare_weyl_gaussianLp {n : ℕ}
    (w : FunctionsMetaplectic.Construction.Metaplectic ℝ n (Gaussian.Construction.realCharacter 1))
    (hw : ∀ (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) x,
      (FunctionsMetaplectic.Construction.weilRepresentation ℝ n (Gaussian.Construction.realCharacter 1) w f).val x =
        (FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter 1) 1 ^ n)⁻¹ *
          FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter 1) (FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter 1)) f.val x)
    (P : SiegelGaussian.Construction.PositiveLagrangianFrame n) :
    ∃ c : ℂ, c ^ 2 * (P.act (Generators.Construction.weylSymplectic ℝ n)).position.det = P.position.det ∧
      RealOscillator.Construction.realL2Oscillator n (Gaussian.Construction.realCharacter 1) w.val P.gaussianLp =
        c • (P.act (Generators.Construction.weylSymplectic ℝ n)).gaussianLp := by
  obtain ⟨c, hc, hF⟩ := P.fourier_gaussianLp
  let γ := FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter 1) 1
  have hγ : γ ^ 2 = Complex.I := FrameGaussianAction.Construction.real_standard_gaussianIndex_square
  have hscalar (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) : w.val.val.2 f =
      (γ ^ n)⁻¹ • (RealFourierFamily.Construction.realFourierOscillatorFamily n 1 one_ne_zero).val.2 f := by
    apply Subtype.ext
    funext x
    change (FunctionsMetaplectic.Construction.weilRepresentation ℝ n (Gaussian.Construction.realCharacter 1) w f).val x =
      (γ ^ n)⁻¹ * ((RealFourierFamily.Construction.realFourierOscillatorFamily n 1 one_ne_zero).val.2 f).val x
    rw [hw, RealGenerators.Construction.real_standard_fourier_oscillator_apply, RealNormalization.Construction.fourierIntegral_real_normalized 1 one_ne_zero]
    simp [γ]
  refine ⟨(γ ^ n)⁻¹ * c, ?_, ?_⟩
  · rw [mul_pow, inv_pow, P.weyl_position_det]
    calc
      _ = ((γ ^ 2) ^ n)⁻¹ * (c ^ 2 * P.quadraticMatrix.det) * P.position.det := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm n 2]
        ring
      _ = P.position.det := by
        rw [hγ, hc, inv_mul_cancel₀ (pow_ne_zero _ Complex.I_ne_zero), one_mul]
  · rw [RealGenerators.Construction.realL2Oscillator_scalar_multiple _ _ _ _ hscalar, hF, smul_smul]

end RepresentationTheory.Weil.Local

namespace RepresentationTheory.Weil.Local.FrameGaussianAction.Construction

/-! The square-normalized Gaussian graph and its oscillator stabilizer. -/

open _root_.Matrix _root_.MeasureTheory

def realGaussianGraph {n : ℕ} (P : SiegelGaussian.Construction.PositiveLagrangianFrame n)
    (v : Lp ℂ 2 (UnitaryInner.Construction.referencePositionMeasure ℝ n)) : Prop :=
  ∃ c : ℂ, c ^ 2 * P.position.det = 1 ∧ v = c • P.gaussianLp

theorem realGaussianGraph_exists {n : ℕ} (P : SiegelGaussian.Construction.PositiveLagrangianFrame n) :
    ∃ v, realGaussianGraph P v := by
  let c : ℂ := (P.position.det⁻¹) ^ (1 / 2 : ℂ)
  refine ⟨c • P.gaussianLp, c, ?_, rfl⟩
  simp only [c, one_div, Complex.cpow_ofNat_inv_pow]
  exact inv_mul_cancel₀ P.position_det_ne_zero

def realGaussianSubgroup (n : ℕ) : Subgroup (FunctionsMetaplectic.Construction.Oscillator ℝ n (Gaussian.Construction.realCharacter 1)) where
  carrier := {a | ∀ P v, realGaussianGraph P v ↔
    realGaussianGraph (P.act (OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter 1) a))
      (RealOscillator.Construction.realL2Oscillator n (Gaussian.Construction.realCharacter 1) a v)}
  one_mem' := by
    intro P v
    rw [map_one, P.act_one, RealOscillator.Construction.realL2Oscillator_one]
    rfl
  mul_mem' := by
    intro a b ha hb P v
    rw [map_mul, P.act_mul, RealOscillator.Construction.realL2Oscillator_mul]
    exact (hb P v).trans (ha _ _)
  inv_mem' := by
    intro a ha P v
    have h := ha (P.act (OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter 1) a⁻¹))
      (RealOscillator.Construction.realL2Oscillator n (Gaussian.Construction.realCharacter 1) a⁻¹ v)
    have hP : (P.act (OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter 1) a⁻¹)).act
        (OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter 1) a) = P := by
      rw [← P.act_mul, map_inv, mul_inv_cancel, P.act_one]
    have hU : RealOscillator.Construction.realL2Oscillator n (Gaussian.Construction.realCharacter 1) a
        (RealOscillator.Construction.realL2Oscillator n (Gaussian.Construction.realCharacter 1) a⁻¹ v) = v := by
      change (RealOscillator.Construction.realL2Oscillator n (Gaussian.Construction.realCharacter 1) a * RealOscillator.Construction.realL2Oscillator n (Gaussian.Construction.realCharacter 1) a⁻¹) v = v
      rw [← RealOscillator.Construction.realL2Oscillator_mul, mul_inv_cancel, RealOscillator.Construction.realL2Oscillator_one]
      rfl
    rw [hP, hU] at h
    exact h.symm

theorem realGaussianSubgroup_mem_of_amplitudes {n : ℕ}
    (a : FunctionsMetaplectic.Construction.Oscillator ℝ n (Gaussian.Construction.realCharacter 1))
    (h : ∀ P : SiegelGaussian.Construction.PositiveLagrangianFrame n, ∃ c : ℂ,
      c ^ 2 * (P.act (OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter 1) a)).position.det = P.position.det ∧
      RealOscillator.Construction.realL2Oscillator n (Gaussian.Construction.realCharacter 1) a P.gaussianLp =
        c • (P.act (OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter 1) a)).gaussianLp) :
    a ∈ realGaussianSubgroup n := by
  intro P v
  obtain ⟨c, hc, hU⟩ := h P
  have hc0 : c ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by decide), zero_mul] at hc
    exact P.position_det_ne_zero hc.symm
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨d * c, ?_, ?_⟩
    · rw [mul_pow, mul_assoc, hc, hd]
    · rw [map_smul, hU, smul_smul]
  · rintro ⟨d, hd, hv⟩
    refine ⟨d / c, ?_, ?_⟩
    · rw [div_pow, ← hc]
      calc
        _ = d ^ 2 * (P.act (OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter 1) a)).position.det := by
          field_simp
        _ = 1 := hd
    · apply (RealOscillator.Construction.realL2Oscillator n (Gaussian.Construction.realCharacter 1) a).injective
      rw [map_smul, hU, smul_smul, div_mul_cancel₀ _ hc0]
      exact hv

theorem realGaussianSubgroup_lower {n : ℕ} (B : FunctionsMetaplectic.Construction.SymmetricMatrix ℝ n) :
    (QuadraticIntertwiner.Construction.realQuadraticMetaplectic 1 B).val ∈ realGaussianSubgroup n := by
  apply realGaussianSubgroup_mem_of_amplitudes
  intro P
  refine ⟨1, ?_, ?_⟩
  · change 1 ^ 2 * (P.act (Generators.Construction.quadraticSymplectic B)).position.det = _
    rw [P.lower_position, one_pow, one_mul]
  · simpa only [one_smul] using! P.lower_gaussianLp B

theorem realGaussianSubgroup_weyl {n : ℕ}
    (w : FunctionsMetaplectic.Construction.Metaplectic ℝ n (Gaussian.Construction.realCharacter 1))
    (hwπ : FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (Gaussian.Construction.realCharacter 1) w = Generators.Construction.weylSymplectic ℝ n)
    (hw : ∀ (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) x,
      (FunctionsMetaplectic.Construction.weilRepresentation ℝ n (Gaussian.Construction.realCharacter 1) w f).val x =
        (FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter 1) 1 ^ n)⁻¹ *
          FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter 1) (FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter 1)) f.val x) :
    w.val ∈ realGaussianSubgroup n := by
  apply realGaussianSubgroup_mem_of_amplitudes
  intro P
  have hproj : OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter 1) w.val = Generators.Construction.weylSymplectic ℝ n := hwπ
  simpa only [hproj] using! P.bare_weyl_gaussianLp w hw

theorem realGaussianSubgroup_minus (n : ℕ) :
    FunctionsMetaplectic.Construction.oscillatorMinus ℝ n (Gaussian.Construction.realCharacter 1) ∈ realGaussianSubgroup n := by
  apply realGaussianSubgroup_mem_of_amplitudes
  intro P
  refine ⟨-1, ?_, ?_⟩
  · change (-1 : ℂ) ^ 2 * (P.act 1).position.det = P.position.det
    rw [P.act_one]
    ring
  · change RealOscillator.Construction.realL2Oscillator n (Gaussian.Construction.realCharacter 1) (FunctionsMetaplectic.Construction.oscillatorMinus ℝ n (Gaussian.Construction.realCharacter 1)) P.gaussianLp =
      (-1 : ℂ) • (P.act 1).gaussianLp
    rw [P.act_one]
    apply RealOscillator.Construction.realL2Oscillator_scalar
    intro f
    change -f = (-1 : ℂ) • f
    exact (neg_one_smul ℂ f).symm

end RepresentationTheory.Weil.Local.FrameGaussianAction.Construction

end

end OAI
