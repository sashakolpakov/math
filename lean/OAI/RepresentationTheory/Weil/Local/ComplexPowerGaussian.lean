import OAI.RepresentationTheory.Weil.Local.PlanarIntegral

/-! # Complex Power Gaussian -/

namespace OAI.RepresentationTheory.Weil.Local.ComplexPowerGaussian.Construction

noncomputable section

section

/-! The actual complex Gaussian limit for every norm power in (0, 1]. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology

theorem planarPowerDamping_one_haar (ε : ℝ) :
    FunctionsMetaplectic.Construction.regularizedGaussian ℂ ArchimedeanTestSpace.Construction.complexStandardCharacter 1 ε =
      (ArchimedeanTestSpace.Construction.complexReferenceHaarFactor : ℂ) * ∫ z, PlanarPowerDamping.Construction.planarPowerDamping 1 ε Real.pi z := by
  rw [FunctionsMetaplectic.Construction.regularizedGaussian, Measure.isAddLeftInvariant_eq_smul_of_regular
    (Measure.addHaar : Measure ℂ) volume, integral_smul_nnreal_measure]
  change (ArchimedeanTestSpace.Construction.complexReferenceHaarFactor : ℂ) *
    (∫ z : ℂ, (Real.exp (-ε * ‖z‖ ^ 2) : ℂ) * ArchimedeanTestSpace.Construction.complexStandardCharacter (1 * z ^ 2 / 2)) = _
  congr 1
  rw [← Complex.volume_preserving_equiv_real_prod.symm.integral_comp
    Complex.measurableEquivRealProd.symm.measurableEmbedding]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    have h := PlanarPowerDamping.Construction.planarPowerDamping_complex 1 ε (Complex.measurableEquivRealProd.symm z)
    have hz : ((Complex.measurableEquivRealProd.symm z).re,
        (Complex.measurableEquivRealProd.symm z).im) = z :=
      Complex.measurableEquivRealProd.apply_symm_apply z
    rw [hz] at h
    simpa only [mul_one, one_mul, Real.rpow_two] using h.symm

theorem planarPowerDamping_one_integral_tendsto :
    Tendsto (fun ε => ∫ z, PlanarPowerDamping.Construction.planarPowerDamping 1 ε Real.pi z) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hr : (ArchimedeanTestSpace.Construction.complexReferenceHaarFactor : ℂ) ≠ 0 := by exact_mod_cast ArchimedeanTestSpace.Construction.complexReferenceHaarFactor_pos.ne'
  have ht := ArchimedeanTestSpace.Construction.regularizedGaussian_complex_standard_tendsto.const_mul (ArchimedeanTestSpace.Construction.complexReferenceHaarFactor : ℂ)⁻¹
  rw [inv_mul_cancel₀ hr] at ht
  apply ht.congr
  intro ε
  rw [planarPowerDamping_one_haar, ← mul_assoc, inv_mul_cancel₀ hr, one_mul]

theorem planarPowerDamping_integral_tendsto (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    Tendsto (fun ε => ∫ z, PlanarPowerDamping.Construction.planarPowerDamping s ε Real.pi z) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have ht := (PlanarIntegral.Construction.planarPowerDamping_integral_difference_tendsto s Real.pi hs hs1 Real.pi_ne_zero).add
    planarPowerDamping_one_integral_tendsto
  simpa only [sub_add_cancel, zero_add] using ht

def complexPowerDamping (s ε : ℝ) (z : ℂ) : ℂ :=
  (Real.exp (-ε * ‖z‖ ^ (2 * s)) : ℂ) * ArchimedeanTestSpace.Construction.complexStandardCharacter (z ^ 2 / 2)

theorem complexPowerDamping_integral_eq_planar (s ε : ℝ) :
    (∫ z : ℂ, complexPowerDamping s ε z) = ∫ z, PlanarPowerDamping.Construction.planarPowerDamping s ε Real.pi z := by
  rw [← Complex.volume_preserving_equiv_real_prod.symm.integral_comp
    Complex.measurableEquivRealProd.symm.measurableEmbedding]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    have h := PlanarPowerDamping.Construction.planarPowerDamping_complex s ε (Complex.measurableEquivRealProd.symm z)
    have hz : ((Complex.measurableEquivRealProd.symm z).re,
        (Complex.measurableEquivRealProd.symm z).im) = z :=
      Complex.measurableEquivRealProd.apply_symm_apply z
    rw [hz] at h
    exact h.symm

theorem complexPowerDamping_integral_tendsto (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    Tendsto (fun ε => ∫ z : ℂ, complexPowerDamping s ε z) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  apply (planarPowerDamping_integral_tendsto s hs hs1).congr
  intro ε
  exact (complexPowerDamping_integral_eq_planar s ε).symm

end

/-! Positive complex Gaussian limits with power damping, for every nontrivial unitary character. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology

def complexRegularizedPowerGaussian (p : ℝ) (ψ : AddChar ℂ ℂ) (a : ℂ) (ε : ℝ) : ℂ :=
  ∫ z : ℂ, (Real.exp (-ε * ‖z‖ ^ (2 * p)) : ℂ) * ψ (a * z ^ 2 / 2) ∂Measure.addHaar

theorem complexRegularizedPowerGaussian_standard_tendsto (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    Tendsto (complexRegularizedPowerGaussian p ArchimedeanTestSpace.Construction.complexStandardCharacter 1) (𝓝[>] (0 : ℝ))
      (𝓝 (ArchimedeanTestSpace.Construction.complexReferenceHaarFactor : ℂ)) := by
  have ht := (complexPowerDamping_integral_tendsto p hp hp1).const_mul (ArchimedeanTestSpace.Construction.complexReferenceHaarFactor : ℂ)
  rw [mul_one] at ht
  apply ht.congr
  intro ε
  rw [complexRegularizedPowerGaussian, Measure.isAddLeftInvariant_eq_smul_of_regular
    (Measure.addHaar : Measure ℂ) volume, integral_smul_nnreal_measure]
  change (ArchimedeanTestSpace.Construction.complexReferenceHaarFactor : ℂ) * (∫ z : ℂ, complexPowerDamping p ε z) =
    (ArchimedeanTestSpace.Construction.complexReferenceHaarFactor : ℂ) * ∫ z : ℂ,
      (Real.exp (-ε * ‖z‖ ^ (2 * p)) : ℂ) * ArchimedeanTestSpace.Construction.complexStandardCharacter (1 * z ^ 2 / 2)
  simp only [one_mul, complexPowerDamping]

theorem complexRegularizedPowerGaussian_substitution
    (p : ℝ) (ψ : AddChar ℂ ℂ) (a q : ℂ) (hq : q ≠ 0)
    (hphase : ∀ z : ℂ, ψ (a * (q * z) ^ 2 / 2) = ArchimedeanTestSpace.Construction.complexStandardCharacter (z ^ 2 / 2)) (ε : ℝ) :
    complexRegularizedPowerGaussian p ψ a ε =
      (addEquivAddHaarChar (ArchimedeanTestSpace.Construction.complexScalarAddEquiv q hq) : ℂ) *
        complexRegularizedPowerGaussian p ArchimedeanTestSpace.Construction.complexStandardCharacter 1 (ε * ‖q‖ ^ (2 * p)) := by
  unfold complexRegularizedPowerGaussian
  rw [ArchimedeanTestSpace.Construction.integral_complex_substitution q hq]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    rw [hphase, one_mul, norm_mul, Real.mul_rpow (norm_nonneg q) (norm_nonneg z)]
    congr 2
    ring_nf

theorem complex_power_gaussian_limit_positive
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (ψ : AddChar ℂ ℂ) (hc : Continuous (fun z => ψ z)) (hu : ∀ z, ‖ψ z‖ = 1)
    (hn : ∃ z, ψ z ≠ 1) (a : ℂ) (ha : a ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ Tendsto (complexRegularizedPowerGaussian p ψ a) (𝓝[>] (0 : ℝ)) (𝓝 (r : ℂ)) := by
  obtain ⟨b, hb⟩ := ArchimedeanTestSpace.Construction.complex_character_coefficient ψ hc hu
  have hb0 : b ≠ 0 := by
    rintro rfl
    obtain ⟨z, hz⟩ := hn
    apply hz
    rw [hb, zero_mul, ArchimedeanTestSpace.Construction.complexStandardCharacter.map_zero_eq_one]
  let q : ℂ := ((b * a)⁻¹) ^ (1 / 2 : ℂ)
  have hsq : q ^ (2 : ℕ) = (b * a)⁻¹ := by simp [q, one_div]
  have hq : q ≠ 0 := by
    intro hq
    rw [hq, zero_pow (by decide)] at hsq
    exact (inv_ne_zero (mul_ne_zero hb0 ha)) hsq.symm
  have hprod : b * a * q ^ 2 = 1 := by rw [hsq, mul_inv_cancel₀ (mul_ne_zero hb0 ha)]
  have hphase (z : ℂ) : ψ (a * (q * z) ^ 2 / 2) = ArchimedeanTestSpace.Construction.complexStandardCharacter (z ^ 2 / 2) := by
    rw [hb]
    congr 1
    calc
      _ = (b * a * q ^ 2) * (z ^ 2 / 2) := by ring
      _ = _ := by rw [hprod, one_mul]
  have hd : 0 < ‖q‖ ^ (2 * p) := Real.rpow_pos_of_pos (norm_pos_iff.mpr hq) _
  have ht : Tendsto (fun ε : ℝ => ε * ‖q‖ ^ (2 * p)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [zero_mul] using h0.mul_const (‖q‖ ^ (2 * p))
    · filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with ε hε
      exact mul_pos hε hd
  let r : ℝ := (addEquivAddHaarChar (ArchimedeanTestSpace.Construction.complexScalarAddEquiv q hq) : ℝ) * ArchimedeanTestSpace.Construction.complexReferenceHaarFactor
  refine ⟨r, mul_pos (addEquivAddHaarChar_pos _) ArchimedeanTestSpace.Construction.complexReferenceHaarFactor_pos, ?_⟩
  have h := ((complexRegularizedPowerGaussian_standard_tendsto p hp hp1).comp ht).const_mul
    (addEquivAddHaarChar (ArchimedeanTestSpace.Construction.complexScalarAddEquiv q hq) : ℂ)
  have hr : (r : ℂ) = (addEquivAddHaarChar (ArchimedeanTestSpace.Construction.complexScalarAddEquiv q hq) : ℂ) *
      (ArchimedeanTestSpace.Construction.complexReferenceHaarFactor : ℂ) := by simp only [r, Complex.ofReal_mul]
  rw [hr]
  exact h.congr fun ε => (complexRegularizedPowerGaussian_substitution p ψ a q hq hphase ε).symm

end

end OAI.RepresentationTheory.Weil.Local.ComplexPowerGaussian.Construction
