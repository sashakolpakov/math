import OAI.Analysis.Fourier.WavePackets.ConvolutionIdentity

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open scoped ENNReal ContDiff RealInnerProductSpace

noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Representatives in the centered unit cube, scaled to the physical side-100 torus. -/
noncomputable def torusInput {n : ℕ} {F : Type*} (f : EuclideanSpace ℝ (Fin n) → F)
    (x : UnitAddTorus (Fin n)) : F :=
  f ((100 : ℝ) • WithLp.toLp 2
    ((UnitAddTorus.measurableEquivPiIoc (fun _ : Fin n => -(1/2 : ℝ))) x).val)

theorem torusInput_coe {n : ℕ} {F : Type*} (f : EuclideanSpace ℝ (Fin n) → F) (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Ioc (-(1/2 : ℝ)) (-(1/2 : ℝ) + 1)) :
    torusInput f (fun i => (x i : UnitAddCircle)) = f ((100 : ℝ) • WithLp.toLp 2 x) := by
  have he : (fun i => (x i : UnitAddCircle)) =
      (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin n => -(1/2 : ℝ))).symm ⟨x, hx⟩ := rfl
  unfold torusInput
  rw [he, MeasurableEquiv.apply_symm_apply]

theorem measurable_torusInput {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : Measurable f) :
    Measurable (torusInput f) := by
  have hc : Continuous (fun x : Fin n → ℝ => (100 : ℝ) • WithLp.toLp 2 x) := by fun_prop
  exact hf.comp (hc.measurable.comp (measurable_subtype_coe.comp
    (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin n => -(1/2 : ℝ))).measurable))

/-- Pairings on the large torus are physical pairings multiplied by its inverse volume. -/
theorem integral_torusInput_pairing {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (hs : Function.support f ⊆ coordinateCube n 5) (g : UnitAddTorus (Fin n) → ℂ) :
    (∫ x, g x * torusInput f x) = ((100 : ℂ) ^ n)⁻¹ *
      ∫ Y, g (torusProjection ((1 / 100 : ℝ) • Y)) * f Y := by
  rw [UnitAddTorus.integral_preimage _ (fun _ : Fin n => -(1/2 : ℝ))]
  have hp : (fun x : Fin n → ℝ => g (fun i => (x i : UnitAddCircle)) *
      torusInput f (fun i => (x i : UnitAddCircle))) =ᵐ[
      volume.restrict {x : Fin n → ℝ | ∀ i, x i ∈ Set.Ioc (-(1/2 : ℝ)) (-(1/2 : ℝ) + 1)}]
      (fun x => g (fun i => (x i : UnitAddCircle)) * f ((100 : ℝ) • WithLp.toLp 2 x)) := by
    apply ae_restrict_of_forall_mem (by measurability)
    intro x hx
    dsimp only
    rw [torusInput_coe f x hx]
  rw [integral_congr_ae hp]
  have hsupport : Function.support (fun x : Fin n → ℝ =>
      g (fun i => (x i : UnitAddCircle)) * f ((100 : ℝ) • WithLp.toLp 2 x)) ⊆
      {x : Fin n → ℝ | ∀ i, x i ∈ Set.Ioc (-(1/2 : ℝ)) (-(1/2 : ℝ) + 1)} := by
    intro x hx i
    have hf : f ((100 : ℝ) • WithLp.toLp 2 x) ≠ 0 := (mul_ne_zero_iff.mp hx).2
    have hi := hs hf i
    change |100 * x i| ≤ 5 at hi
    constructor <;> nlinarith [abs_le.mp hi]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    by_contra hfx
    exact hx (hsupport hfx))]
  have hchange := (PiLp.volume_preserving_ofLp (Fin n)).integral_comp
    (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).measurableEmbedding
    (fun x : Fin n → ℝ => g (fun i => (x i : UnitAddCircle)) * f ((100 : ℝ) • WithLp.toLp 2 x))
  rw [← hchange]
  have hpoint (x : EuclideanSpace ℝ (Fin n)) :
      g (fun i => (x i : UnitAddCircle)) * f ((100 : ℝ) • x) =
      (fun Y => g (torusProjection ((1 / 100 : ℝ) • Y)) * f Y) ((100 : ℝ) • x) := by
    have he : (1 / 100 : ℝ) • ((100 : ℝ) • x) = x := by module
    dsimp only
    rw [he]
    rfl
  simp_rw [hpoint]
  have hi := Measure.integral_comp_smul_of_nonneg volume
    (fun Y : EuclideanSpace ℝ (Fin n) => g (torusProjection ((1 / 100 : ℝ) • Y)) * f Y)
    (100 : ℝ) (hR := by norm_num)
  simpa only [finrank_euclideanSpace, Fintype.card_fin, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_ofNat] using hi

theorem lintegral_torusInput {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (hs : Function.support f ⊆ coordinateCube n 5) :
    (∫⁻ x, torusInput f x) = ((100 : ℝ≥0∞) ^ n)⁻¹ * ∫⁻ Y, f Y := by
  rw [UnitAddTorus.lintegral_preimage _ (fun _ : Fin n => -(1/2 : ℝ))]
  have hp : (fun x : Fin n → ℝ => torusInput f (fun i => (x i : UnitAddCircle))) =ᵐ[
      volume.restrict {x : Fin n → ℝ | ∀ i, x i ∈ Set.Ioc (-(1/2 : ℝ)) (-(1/2 : ℝ) + 1)}]
      (fun x => f ((100 : ℝ) • WithLp.toLp 2 x)) := by
    apply ae_restrict_of_forall_mem (by measurability)
    intro x hx
    exact torusInput_coe f x hx
  rw [lintegral_congr_ae hp]
  have hsupport : Function.support (fun x : Fin n → ℝ => f ((100 : ℝ) • WithLp.toLp 2 x)) ⊆
      {x : Fin n → ℝ | ∀ i, x i ∈ Set.Ioc (-(1/2 : ℝ)) (-(1/2 : ℝ) + 1)} := by
    intro x hx i
    have hi := hs hx i
    change |100 * x i| ≤ 5 at hi
    constructor <;> nlinarith [abs_le.mp hi]
  rw [setLIntegral_eq_of_support_subset hsupport]
  have hchange := (PiLp.volume_preserving_ofLp (Fin n)).lintegral_comp_emb
    (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).measurableEmbedding
    (fun x : Fin n → ℝ => f ((100 : ℝ) • WithLp.toLp 2 x))
  rw [← hchange]
  have hi := lintegral_map_equiv (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) f
    (Homeomorph.smulOfNeZero (100 : ℝ) (by norm_num)).toMeasurableEquiv
  change (∫⁻ x, f x ∂Measure.map (fun x => (100 : ℝ) • x) volume) =
    (∫⁻ x, f ((100 : ℝ) • x)) at hi
  change (∫⁻ x, f ((100 : ℝ) • x)) = _
  rw [← hi]
  rw [Measure.map_addHaar_smul volume (by norm_num), lintegral_smul_measure]
  simp [finrank_euclideanSpace, ENNReal.ofReal_pow, ENNReal.ofReal_inv_of_pos]

theorem eLpNorm_torusInput {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (hm : Measurable f) (hs : Function.support f ⊆ coordinateCube n 5)
    {p : ℝ≥0∞} (hp : p ≠ 0) (hptop : p ≠ ⊤) :
    eLpNorm (torusInput f) p volume =
      (((100 : ℝ≥0∞) ^ n)⁻¹) ^ (1 / p.toReal) * eLpNorm f p volume := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hptop
      (measurable_torusInput hm).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp hptop hm.aestronglyMeasurable]
  have hsp : Function.support (fun x => ‖f x‖ₑ ^ p.toReal) ⊆ coordinateCube n 5 := by
    intro x hx
    apply hs
    intro hf
    apply hx
    simp [hf, ENNReal.toReal_pos hp hptop]
  have he : (fun x => ‖torusInput f x‖ₑ ^ p.toReal) =
      torusInput (fun x => ‖f x‖ₑ ^ p.toReal) := rfl
  rw [he, lintegral_torusInput _ hsp, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]

theorem integrable_torusInput {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hm : Measurable f) (hf : Integrable f)
    (hs : Function.support f ⊆ coordinateCube n 5) : Integrable (torusInput f) := by
  apply memLp_one_iff_integrable.mp
  change eLpNorm (torusInput f) 1 volume < ⊤
  rw [eLpNorm_torusInput f hm hs one_ne_zero ENNReal.one_ne_top]
  apply ENNReal.mul_lt_top
  · norm_num; positivity
  · exact (memLp_one_iff_integrable.mpr hf).eLpNorm_lt_top

theorem torusProjection_sub {n : ℕ} (X Y : EuclideanSpace ℝ (Fin n)) :
    torusProjection X - torusProjection Y = torusProjection (X - Y) := by
  ext i
  simp [torusProjection]

/-- The actual periodic and Euclidean half-waves differ on the observation
cube by precisely the already estimated periodization error. -/
theorem periodicHalfWave_local_comparison {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hs : HasCompactSupport φ) (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport φ)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hm : Measurable f) (hf : Integrable f)
    (hsf : Function.support f ⊆ coordinateCube n 5)
    {h T : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (hT₀ : 0 ≤ T) (hT₁ : T ≤ 2)
    {X : EuclideanSpace ℝ (Fin n)} (hX : X ∈ coordinateCube n (1 / 2)) :
    periodicHalfWave φ h T (torusInput f) (torusProjection ((1 / 100 : ℝ) • X)) =
      OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h T f X +
        (((2 * Real.pi : ℝ) : ℂ) ^ n)⁻¹ * periodizationError volume φ f h T X := by
  obtain ⟨C, hC, hb⟩ := periodizationError_bound (μ := volume) hφ hzero hs 0
  have hR := (hb f hf (Filter.Eventually.of_forall fun Y hY => hsf hY)
    X T h hX hT₀ hT₁ hh hh₁).1
  have hK := (frequencyHalfWave_eq_integral_kernel hφ.continuous hs hh T hf X).1
  rw [periodicHalfWave_eq_kernel_integral hs hh T (integrable_torusInput hm hf hsf),
    integral_torusInput_pairing f hsf]
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero n (by norm_num)), one_mul]
  have hq (Y : EuclideanSpace ℝ (Fin n)) :
      torusProjection ((1 / 100 : ℝ) • X) - torusProjection ((1 / 100 : ℝ) • Y) =
        torusProjection ((1 / 100 : ℝ) • (X - Y)) := by
    rw [torusProjection_sub, smul_sub]
  simp_rw [hq, periodicKernel_eq_kernel_add_remainder hs hφ hzero hh, mul_assoc,
    add_mul]
  rw [integral_const_mul, integral_add hK hR,
    (frequencyHalfWave_eq_integral_kernel hφ.continuous hs hh T hf X).2]
  unfold periodizationError
  ring

end OAI.Analysis.Fourier.WavePackets
