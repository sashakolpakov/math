import OAI.RepresentationTheory.Weil.Local.RealNormalization
import OAI.RepresentationTheory.Weil.Local.RealCover

/-! # Real Fourier Family -/

namespace OAI.RepresentationTheory.Weil.Local.RealFourierFamily.Construction

noncomputable section

/-! The normalized real Fourier operator for every nonzero character parameter. -/

open _root_.MeasureTheory

def realFrequencyAddEquiv (n : ℕ) (c : ℝ) (hc : c ≠ 0) :
    FunctionsMetaplectic.Construction.Position ℝ n ≃ₜ+ FunctionsMetaplectic.Construction.Position ℝ n :=
  (LinearEquiv.smulOfNeZero ℝ (FunctionsMetaplectic.Construction.Position ℝ n) c hc).toContinuousLinearEquiv.toContinuousAddEquiv

def realFourierScale (n : ℕ) (c : ℝ) : ℝ := Real.sqrt |c| ^ n

theorem realFourierScale_pos (n : ℕ) (c : ℝ) (hc : c ≠ 0) : 0 < realFourierScale n c :=
  pow_pos (Real.sqrt_pos.mpr (abs_pos.mpr hc)) n

def realFourierScaleUnit (n : ℕ) (c : ℝ) (hc : c ≠ 0) : ℂˣ :=
  Units.mk0 (realFourierScale n c : ℂ)
    (Complex.ofReal_ne_zero.mpr (realFourierScale_pos n c hc).ne')

def realNormalizedFourier (n : ℕ) (c : ℝ) (hc : c ≠ 0) :
    FunctionsMetaplectic.Construction.schwartzBruhat ℝ n ≃ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat ℝ n :=
  ((RealFourierLp.Construction.realBruhatFourier n).trans (FunctionsMetaplectic.Construction.schwartzBruhat_coordinateEquiv (realFrequencyAddEquiv n c hc))).trans
    (LinearEquiv.smulOfUnit (realFourierScaleUnit n c hc))

theorem realNormalizedFourier_apply {n : ℕ} (c : ℝ) (hc : c ≠ 0)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    (realNormalizedFourier n c hc f).val x =
      FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) (FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c)) f.val x := by
  change (realFourierScale n c : ℂ) * (RealFourierLp.Construction.realBruhatFourier n f).val (c • x) = _
  rw [RealNormalization.Construction.fourierIntegral_real_normalized c hc, RealNormalization.Construction.real_fourier_frequency, RealFourierLp.Construction.realBruhatFourier_apply,
    Complex.real_smul]
  rfl

theorem realFourierScale_square (n : ℕ) (c : ℝ) (hc : c ≠ 0) :
    realFourierScale n c ^ 2 * (|c| ^ n)⁻¹ = 1 := by
  rw [realFourierScale, pow_two, ← mul_pow, Real.mul_self_sqrt (abs_nonneg _),
    mul_inv_cancel₀ (pow_ne_zero _ (abs_ne_zero.mpr hc))]

theorem realNormalizedFourier_plancherel {n : ℕ} (c : ℝ) (hc : c ≠ 0)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) :
    (∫ x, ‖(realNormalizedFourier n c hc f).val x‖ ^ 2) = ∫ x, ‖f.val x‖ ^ 2 := by
  have hval (x : FunctionsMetaplectic.Construction.Position ℝ n) : (realNormalizedFourier n c hc f).val x =
      (realFourierScale n c : ℂ) * FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter 1) volume f.val (c • x) := by
    change (realFourierScale n c : ℂ) * (RealFourierLp.Construction.realBruhatFourier n f).val (c • x) = _
    rw [RealFourierLp.Construction.realBruhatFourier_apply]
  simp_rw [hval, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (realFourierScale_pos n c hc), mul_pow]
  rw [integral_const_mul]
  have h := Measure.integral_comp_smul (volume : Measure (FunctionsMetaplectic.Construction.Position ℝ n))
    (fun x => ‖FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter 1) volume f.val x‖ ^ 2) c
  simp only [Module.finrank_pi, Fintype.card_fin, abs_inv, abs_pow, smul_eq_mul] at h
  rw [h, ← mul_assoc, realFourierScale_square n c hc, one_mul]
  exact RealFourierLp.Construction.real_fourier_plancherel_standard f

theorem realNormalizedFourier_unitary {n : ℕ} (c : ℝ) (hc : c ≠ 0)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) :
    FunctionsMetaplectic.Construction.l2Energy ℝ n (realNormalizedFourier n c hc f) = FunctionsMetaplectic.Construction.l2Energy ℝ n f := by
  let μ : Measure (FunctionsMetaplectic.Construction.Position ℝ n) := Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure ℝ))
  have h := Measure.isAddLeftInvariant_eq_smul_of_regular μ volume
  change (∫ x, ‖(realNormalizedFourier n c hc f).val x‖ ^ 2 ∂μ) = ∫ x, ‖f.val x‖ ^ 2 ∂μ
  rw [h, integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  congr 1
  exact realNormalizedFourier_plancherel c hc f

theorem realNormalizedFourier_intertwines {n : ℕ} (c : ℝ) (hc : c ≠ 0)
    (v : FunctionsMetaplectic.Construction.PhaseSpace ℝ n) (f h : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) :
    FunctionsMetaplectic.Construction.heisenbergGraph (Gaussian.Construction.realCharacter c) v f h ↔
      FunctionsMetaplectic.Construction.heisenbergGraph (Gaussian.Construction.realCharacter c) (FunctionsMetaplectic.Construction.symplecticAction (Generators.Construction.weylSymplectic ℝ n) v)
        (realNormalizedFourier n c hc f) (realNormalizedFourier n c hc h) := by
  let : (FunctionsMetaplectic.Construction.selfDualMeasure ℝ (Gaussian.Construction.realCharacter c)).IsAddHaarMeasure :=
    FourierTools.Construction.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℝ (Gaussian.Construction.realCharacter c)
      (RealFourierLp.Construction.fourierHaarScaleSquared_real_pos c hc)
  let : (FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c)).IsAddHaarMeasure := by
    unfold FunctionsMetaplectic.Construction.positionMeasure
    infer_instance
  let hf : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n :=
    ⟨FunctionsMetaplectic.Construction.heisenbergFunction (Gaussian.Construction.realCharacter c) v f.val, FourierEquivalence.Construction.real_heisenberg_mem c v f⟩
  have hcov : (realNormalizedFourier n c hc hf).val =
      FunctionsMetaplectic.Construction.heisenbergFunction (Gaussian.Construction.realCharacter c) (FunctionsMetaplectic.Construction.symplecticAction (Generators.Construction.weylSymplectic ℝ n) v)
        (realNormalizedFourier n c hc f).val := by
    have heq (g : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) : (realNormalizedFourier n c hc g).val =
        FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) (FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c)) g.val :=
      funext (realNormalizedFourier_apply c hc g)
    rw [heq, heq]
    exact FourierEquivalence.Construction.fourierIntegral_heisenberg (Gaussian.Construction.realCharacter c) (FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c)) v f.val
  unfold FunctionsMetaplectic.Construction.heisenbergGraph
  rw [← hcov]
  change h.val = hf.val ↔
    (realNormalizedFourier n c hc h).val = (realNormalizedFourier n c hc hf).val
  constructor
  · intro hh
    rw [Subtype.ext hh]
  · intro hh
    exact congrArg Subtype.val ((realNormalizedFourier n c hc).injective (Subtype.ext hh))

def realFourierOscillatorFamily (n : ℕ) (c : ℝ) (hc : c ≠ 0) : FunctionsMetaplectic.Construction.Oscillator ℝ n (Gaussian.Construction.realCharacter c) :=
  ⟨(Generators.Construction.weylSymplectic ℝ n, realNormalizedFourier n c hc),
    ⟨realNormalizedFourier_unitary c hc, realNormalizedFourier_intertwines c hc⟩⟩

theorem real_metaplecticProjection_surjective_parameter (n : ℕ) (c : ℝ) (hc : c ≠ 0) :
    Function.Surjective (FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (Gaussian.Construction.realCharacter c)) := by
  apply MonoidHom.range_eq_top.mp
  apply GenerationSymplectic.Construction.subgroup_eq_top_of_symplectic_unipotents
  · intro B
    let u := QuadraticIntertwiner.Construction.realQuadraticMetaplectic c ⟨-B.val, B.property.neg⟩
    let w := realFourierOscillatorFamily n c hc
    have h : w⁻¹ * u.val * w ∈ FunctionsMetaplectic.Construction.metaplecticSubgroup ℝ n (Gaussian.Construction.realCharacter c) := by
      have hh := (inferInstance : (FunctionsMetaplectic.Construction.metaplecticSubgroup ℝ n (Gaussian.Construction.realCharacter c)).Normal).conj_mem
        u.val u.property w⁻¹
      simpa only [inv_inv] using hh
    refine ⟨⟨w⁻¹ * u.val * w, h⟩, ?_⟩
    change OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter c) (w⁻¹ * u.val * w) = GenerationSymplectic.Construction.upperSymplectic B
    rw [map_mul, map_mul, map_inv]
    exact (OscillatorProjection.Construction.upper_quadratic_conjugation ℝ n B).symm
  · intro B
    exact ⟨QuadraticIntertwiner.Construction.realQuadraticMetaplectic c B, rfl⟩

theorem real_metaplecticProjection_surjective
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t => ψ t))
    (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1) (n : ℕ) :
    Function.Surjective (FunctionsMetaplectic.Construction.metaplecticProjection ℝ n ψ) := by
  obtain ⟨c, hc', rfl⟩ := RealCharacters.Construction.continuous_nontrivial_unitary_real_character ψ hc hu hn
  exact real_metaplecticProjection_surjective_parameter n c hc'

end

end OAI.RepresentationTheory.Weil.Local.RealFourierFamily.Construction
