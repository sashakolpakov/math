import OAI.RepresentationTheory.Weil.UnitarySplitting.FourierInvolution
import OAI.RepresentationTheory.Weil.UnitarySplitting.Weak

/-! # Fourier Pairing -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.FourierPairing.Construction

noncomputable section

section

/-! The Fourier adjoint identity from an absolutely integrable double
integral, used to determine the positive normalization scalar. -/

open _root_.MeasureTheory
open scoped ComplexConjugate InnerProductSpace

theorem fourier_integral_pairing
    {F : Type} [NormedField F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] {d : ℕ}
    (ψ : AddChar F ℂ) (hψ : Continuous (fun t : F => ψ t)) (hunit : ∀ t, ‖ψ t‖ = 1)
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position F d)) [SFinite μ]
    (f g : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hfc : Continuous f) (hgc : Continuous g) :
    (∫ x, g x * conj (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x) ∂μ) =
      ∫ y, Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ g (-y) * conj (f y) ∂μ := by
  let k : Local.FunctionsMetaplectic.Construction.Position F d × Local.FunctionsMetaplectic.Construction.Position F d → ℂ :=
    fun z => g z.1 * conj (f z.2 * ψ (-Local.FunctionsMetaplectic.Construction.dot z.1 z.2))
  have hk : Integrable k (μ.prod μ) := by
    have hkc : Continuous k := by
      dsimp [k, Local.FunctionsMetaplectic.Construction.dot]
      fun_prop
    apply (hg.norm.mul_prod hf.norm).mono hkc.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun z => by
      simp only [k, norm_mul, RCLike.norm_conj, hunit, mul_one, norm_norm, le_refl]
  calc
    _ = ∫ x, ∫ y, g x * conj (f y * ψ (-Local.FunctionsMetaplectic.Construction.dot x y)) ∂μ ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [integral_const_mul, integral_conj]
        rfl
    _ = ∫ y, ∫ x, g x * conj (f y * ψ (-Local.FunctionsMetaplectic.Construction.dot x y)) ∂μ ∂μ :=
      integral_integral_swap hk
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        dsimp only
        unfold Local.FunctionsMetaplectic.Construction.fourierIntegral
        rw [← integral_mul_const]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          dsimp only
          have hp : conj (ψ (-Local.FunctionsMetaplectic.Construction.dot x y)) = ψ (-Local.FunctionsMetaplectic.Construction.dot (-y) x) := by
            have hd : -Local.FunctionsMetaplectic.Construction.dot (-y) x = Local.FunctionsMetaplectic.Construction.dot x y := by simp [Local.FunctionsMetaplectic.Construction.dot, mul_comm]
            rw [hd, ψ.map_neg_eq_inv, Complex.inv_eq_conj (hunit _), starRingEnd_self_apply]
          rw [map_mul, hp]
          ring

theorem ultraFourier_inner
    {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [IsUltrametricDist F] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
    (hc : Continuous (fun t : F => ψ t)) (hunit : ∀ t, ‖ψ t‖ = 1)
    (hnontrivial : ∃ t, ψ t ≠ 1) (f g : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    ⟪Weak.Construction.testToL2 F d (FourierUltra.Construction.ultraFourierLinearMap hF ψ hc hunit hnontrivial (Weak.Construction.referencePositionMeasure F d) f),
      Weak.Construction.testToL2 F d g⟫_ℂ =
    ⟪Weak.Construction.testToL2 F d f, Weak.Construction.testToL2 F d (FourierInvolution.Construction.bruHatReflection d
      (FourierUltra.Construction.ultraFourierLinearMap hF ψ hc hunit hnontrivial (Weak.Construction.referencePositionMeasure F d) g))⟫_ℂ := by
  rw [Weak.Construction.testToL2_inner, Weak.Construction.testToL2_inner]
  exact fourier_integral_pairing ψ hc hunit (Weak.Construction.referencePositionMeasure F d) f.val g.val
    (TestSpaceAnalysis.Construction.schwartzBruhat_integrable _ f) (TestSpaceAnalysis.Construction.schwartzBruhat_integrable _ g)
    (TestSpaceAnalysis.Construction.schwartzBruhat_continuous f.property) (TestSpaceAnalysis.Construction.schwartzBruhat_continuous g.property)

end

section

/-! Positive Fourier normalization and a unitary Fourier automorphism
on the nonarchimedean Bruhat space. -/

open _root_.MeasureTheory
open scoped InnerProductSpace

variable {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F]
variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
variable [IsUltrametricDist F] [CharZero F] {d : ℕ}
variable (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
variable (hc : Continuous (fun t : F => ψ t)) (hunit : ∀ t, ‖ψ t‖ = 1)
variable (hnontrivial : ∃ t, ψ t ≠ 1)

theorem ultraFourier_positive_scalar :
    ∃ r : ℝ, 0 < r ∧ ∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d,
      FourierInvolution.Construction.bruHatReflection d (FourierUltra.Construction.ultraFourierLinearMap hF ψ hc hunit hnontrivial (Weak.Construction.referencePositionMeasure F d)
        (FourierUltra.Construction.ultraFourierLinearMap hF ψ hc hunit hnontrivial (Weak.Construction.referencePositionMeasure F d) f)) =
          (r : ℂ) • f := by
  let T := FourierUltra.Construction.ultraFourierLinearMap hF ψ hc hunit hnontrivial (Weak.Construction.referencePositionMeasure F d)
  obtain ⟨z, -, hz⟩ := FourierInvolution.Construction.ultraFourier_square_scalar hF ψ hc hunit hnontrivial
    (Weak.Construction.referencePositionMeasure F d)
  obtain ⟨u, hu⟩ := LocalTest.Construction.exists_test_nonzero F hF d
  have hTu : T u ≠ 0 := by
    intro hh
    apply hu
    apply FourierUltra.Construction.ultraFourierLinearMap_injective hF ψ hc hunit hnontrivial (Weak.Construction.referencePositionMeasure F d)
    rw [map_zero]
    exact hh
  have hnorm (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (hf : f ≠ 0) : 0 < ‖Weak.Construction.testToL2 F d f‖ := by
    apply norm_pos_iff.mpr
    intro hh
    apply hf
    apply Weak.Construction.testToL2_injective F d
    rw [map_zero]
    exact hh
  let r : ℝ := ‖Weak.Construction.testToL2 F d (T u)‖ ^ 2 / ‖Weak.Construction.testToL2 F d u‖ ^ 2
  have hr : 0 < r := div_pos (sq_pos_of_pos (hnorm (T u) hTu)) (sq_pos_of_pos (hnorm u hu))
  have heq : z = (r : ℂ) := by
    have hh := ultraFourier_inner hF ψ hc hunit hnontrivial u (T u)
    rw [hz, map_smul, inner_smul_right, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K] at hh
    change z = ((‖Weak.Construction.testToL2 F d (T u)‖ ^ 2 / ‖Weak.Construction.testToL2 F d u‖ ^ 2 : ℝ) : ℂ)
    rw [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_pow]
    apply (eq_div_iff (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (hnorm u hu).ne'))).mpr
    exact hh.symm
  refine ⟨r, hr, fun f => ?_⟩
  rw [← heq]
  exact hz f

omit [CompleteSpace F] [IsUltrametricDist F] [CharZero F] in
theorem testToL2_norm_sq (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    ‖Weak.Construction.testToL2 F d f‖ ^ 2 = Local.FunctionsMetaplectic.Construction.l2Energy F d f := by
  rw [Weak.Construction.testToL2_norm, Real.sq_sqrt]
  exact integral_nonneg (fun x => sq_nonneg ‖f.val x‖)

omit [CompleteSpace F] [IsUltrametricDist F] [CharZero F] in
theorem l2Energy_smul (a : ℂ) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    Local.FunctionsMetaplectic.Construction.l2Energy F d (a • f) = ‖a‖ ^ 2 * Local.FunctionsMetaplectic.Construction.l2Energy F d f := by
  rw [← testToL2_norm_sq, map_smul, norm_smul, mul_pow, testToL2_norm_sq]

omit [CharZero F] in
theorem ultraFourier_energy_scale (r : ℝ)
    (hscalar : ∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d,
      FourierInvolution.Construction.bruHatReflection d (FourierUltra.Construction.ultraFourierLinearMap hF ψ hc hunit hnontrivial (Weak.Construction.referencePositionMeasure F d)
        (FourierUltra.Construction.ultraFourierLinearMap hF ψ hc hunit hnontrivial (Weak.Construction.referencePositionMeasure F d) f)) =
          (r : ℂ) • f) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    Local.FunctionsMetaplectic.Construction.l2Energy F d (FourierUltra.Construction.ultraFourierLinearMap hF ψ hc hunit hnontrivial (Weak.Construction.referencePositionMeasure F d) f) =
      r * Local.FunctionsMetaplectic.Construction.l2Energy F d f := by
  let T := FourierUltra.Construction.ultraFourierLinearMap hF ψ hc hunit hnontrivial (Weak.Construction.referencePositionMeasure F d)
  have hh := ultraFourier_inner hF ψ hc hunit hnontrivial f (T f)
  rw [hscalar, map_smul, inner_smul_right, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K] at hh
  have hh' : (‖Weak.Construction.testToL2 F d (T f)‖ : ℂ) ^ 2 = (r : ℂ) * (‖Weak.Construction.testToL2 F d f‖ : ℂ) ^ 2 := hh
  have hr : ‖Weak.Construction.testToL2 F d (T f)‖ ^ 2 = r * ‖Weak.Construction.testToL2 F d f‖ ^ 2 := by
    exact_mod_cast hh'
  simpa only [testToL2_norm_sq] using hr

include hF hunit hnontrivial in
theorem exists_ultra_unitary_fourier :
    ∃ U : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d,
      (∀ f, Local.FunctionsMetaplectic.Construction.l2Energy F d (U f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f) ∧
      (∀ v f, U (UltraMultiplier.Construction.ultraHeisenbergOperator ψ hc v f) =
        UltraMultiplier.Construction.ultraHeisenbergOperator ψ hc (FourierCovariance.Construction.fourierPhaseRotation v) (U f)) := by
  obtain ⟨r, hr, hscalar⟩ := ultraFourier_positive_scalar hF ψ hc hunit hnontrivial
  let a : ℂ := ((Real.sqrt r)⁻¹ : ℝ)
  have ha : a ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos.mpr hr).ne')
  let T := FourierInvolution.Construction.ultraFourierEquiv hF ψ hc hunit hnontrivial (Weak.Construction.referencePositionMeasure F d)
  let U := T.trans (LinearEquiv.smulOfUnit (Units.mk0 a ha))
  have hU (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
      U f = a • FourierUltra.Construction.ultraFourierLinearMap hF ψ hc hunit hnontrivial (Weak.Construction.referencePositionMeasure F d) f := rfl
  refine ⟨U, ?_, ?_⟩
  · intro f
    rw [hU, l2Energy_smul, ultraFourier_energy_scale hF ψ hc hunit hnontrivial r hscalar]
    have hscale : ‖a‖ ^ 2 * r = 1 := by
      have hroot := Real.sq_sqrt hr.le
      dsimp [a]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hr))]
      rw [inv_pow, hroot, inv_mul_cancel₀ hr.ne']
    rw [← mul_assoc, hscale, one_mul]
  · intro v f
    rw [hU, FourierInvolution.Construction.ultraFourier_covariance, hU, map_smul]

end

/-! Two test functions that agree on the support of a nonzero one cannot
have disjoint Fourier supports. This detects nonzero Gaussian constants. -/

open _root_.MeasureTheory
open scoped InnerProductSpace ComplexConjugate

theorem ultra_fourier_common_support
    {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [IsUltrametricDist F] [CharZero F] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
    (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
    (hn : ∃ x : F, ψ x ≠ 1)
    (f g : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (hf : f ≠ 0)
    (hagree : ∀ x, f.val x ≠ 0 → g.val x = f.val x) :
    ∃ y, (FourierUltra.Construction.ultraFourierLinearMap hF ψ hc hu hn (Weak.Construction.referencePositionMeasure F d) f).val y ≠ 0 ∧
      (FourierUltra.Construction.ultraFourierLinearMap hF ψ hc hu hn (Weak.Construction.referencePositionMeasure F d) g).val y ≠ 0 := by
  let T := FourierUltra.Construction.ultraFourierLinearMap hF ψ hc hu hn (Weak.Construction.referencePositionMeasure F d)
  obtain ⟨r, hr, hscalar⟩ := ultraFourier_positive_scalar (d := d) hF ψ hc hu hn
  by_contra! hdisjoint
  have hzero : ⟪Weak.Construction.testToL2 F d (T g), Weak.Construction.testToL2 F d (T f)⟫_ℂ = 0 := by
    rw [Weak.Construction.testToL2_inner]
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun y => by
      change (T f).val y * conj ((T g).val y) = 0
      by_cases hy : (T f).val y = 0
      · rw [hy, zero_mul]
      · have hz : (T g).val y = 0 := hdisjoint y hy
        rw [hz, map_zero, mul_zero]
  have hcross : ⟪Weak.Construction.testToL2 F d g, Weak.Construction.testToL2 F d f⟫_ℂ =
      ⟪Weak.Construction.testToL2 F d f, Weak.Construction.testToL2 F d f⟫_ℂ := by
    rw [Weak.Construction.testToL2_inner, Weak.Construction.testToL2_inner]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : f.val x = 0
      · simp only [hx, zero_mul]
      · rw [hagree x hx]
  have hh := ultraFourier_inner hF ψ hc hu hn g (T f)
  rw [hscalar, map_smul, inner_smul_right, hcross] at hh
  change ⟪Weak.Construction.testToL2 F d (T g), Weak.Construction.testToL2 F d (T f)⟫_ℂ = _ at hh
  rw [hzero, inner_self_eq_norm_sq_to_K] at hh
  have hfn : Weak.Construction.testToL2 F d f ≠ 0 := by
    intro hz
    exact hf ((Weak.Construction.testToL2_injective F d) (by simpa only [map_zero] using hz))
  exact (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne')
    (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr hfn).ne'))) hh.symm

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.FourierPairing.Construction
