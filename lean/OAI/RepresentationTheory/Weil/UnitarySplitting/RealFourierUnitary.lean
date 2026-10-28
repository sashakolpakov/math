import OAI.RepresentationTheory.Weil.UnitarySplitting.RealFourier
import OAI.RepresentationTheory.Weil.UnitarySplitting.FourierPairing

/-! # Real Fourier Unitary -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.RealFourierUnitary.Construction

noncomputable section

/-! The unitary Fourier lift for every nontrivial continuous unitary
character of the real field. -/

open _root_.MeasureTheory

theorem real_nondiscrete : ¬ DiscreteTopology ℝ := by
  intro h
  let : DiscreteTopology ℝ := h
  have : Subsingleton ℝ := subsingleton_of_preconnected_totallyDisconnected
  exact zero_ne_one (Subsingleton.elim (0 : ℝ) 1)

def realPositionDilation (d : ℕ) (c : ℝ) (hc : c ≠ 0) : Local.FunctionsMetaplectic.Construction.Position ℝ d ≃ₜ+ Local.FunctionsMetaplectic.Construction.Position ℝ d :=
  (LinearEquiv.smulOfUnit (Units.mk0 c hc) : Local.FunctionsMetaplectic.Construction.Position ℝ d ≃ₗ[ℝ] Local.FunctionsMetaplectic.Construction.Position ℝ d)
    |>.toContinuousLinearEquiv.toContinuousAddEquiv

def realRawFourier (d : ℕ) (c : ℝ) (hc : c ≠ 0) : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d :=
  (RealFourier.Construction.realBruhatFourier d).trans (CoordinateChange.Construction.schwartzBruhat_coordinateEquiv (realPositionDilation d c hc))

theorem real_fourier_frequency {d : ℕ} (c : ℝ) (f : Local.FunctionsMetaplectic.Construction.Position ℝ d → ℂ) (x : Local.FunctionsMetaplectic.Construction.Position ℝ d) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral (RealFourier.Construction.realCharacter c) volume f x =
      Local.FunctionsMetaplectic.Construction.fourierIntegral (RealFourier.Construction.realCharacter 1) volume f (c • x) := by
  unfold Local.FunctionsMetaplectic.Construction.fourierIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    congr 1
    change (Real.fourierChar (c * -Local.FunctionsMetaplectic.Construction.dot x y) : ℂ) =
      (Real.fourierChar (1 * -Local.FunctionsMetaplectic.Construction.dot (c • x) y) : ℂ)
    congr 2
    simp [Local.FunctionsMetaplectic.Construction.dot, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_assoc]

theorem realRawFourier_apply {d : ℕ} (c : ℝ) (hc : c ≠ 0)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) (x : Local.FunctionsMetaplectic.Construction.Position ℝ d) :
    (realRawFourier d c hc f).val x = Local.FunctionsMetaplectic.Construction.fourierIntegral (RealFourier.Construction.realCharacter c) volume f.val x := by
  change (RealFourier.Construction.realBruhatFourier d f).val (c • x) = _
  rw [RealFourier.Construction.realBruhatFourier_apply, ← real_fourier_frequency c]

theorem realRawFourier_energy {d : ℕ} (c : ℝ) (hc : c ≠ 0) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) :
    Local.FunctionsMetaplectic.Construction.l2Energy ℝ d (realRawFourier d c hc f) = (|c| ^ d)⁻¹ * Local.FunctionsMetaplectic.Construction.l2Energy ℝ d f := by
  change (∫ x, ‖(RealFourier.Construction.realBruhatFourier d f).val (c • x)‖ ^ 2 ∂ Weak.Construction.referencePositionMeasure ℝ d) = _
  have hh := Measure.integral_comp_smul (Weak.Construction.referencePositionMeasure ℝ d)
    (fun x : Local.FunctionsMetaplectic.Construction.Position ℝ d => ‖(RealFourier.Construction.realBruhatFourier d f).val x‖ ^ 2) c
  have hh' : (∫ x, ‖(RealFourier.Construction.realBruhatFourier d f).val (c • x)‖ ^ 2 ∂ Weak.Construction.referencePositionMeasure ℝ d) =
      (|c| ^ d)⁻¹ * Local.FunctionsMetaplectic.Construction.l2Energy ℝ d (RealFourier.Construction.realBruhatFourier d f) := by
    simpa only [Module.finrank_pi, Fintype.card_fin, abs_inv, abs_pow, smul_eq_mul,
      Local.FunctionsMetaplectic.Construction.l2Energy] using hh
  exact hh'.trans (congrArg ((|c| ^ d)⁻¹ * ·) (RealFourier.Construction.realBruhatFourier_unitary f))

theorem exists_real_unitary_fourier {d : ℕ}
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t : ℝ => ψ t))
    (hunit : ∀ t, ‖ψ t‖ = 1) (hnontrivial : ∃ t, ψ t ≠ 1) :
    ∃ U : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d,
      (∀ f, Local.FunctionsMetaplectic.Construction.l2Energy ℝ d (U f) = Local.FunctionsMetaplectic.Construction.l2Energy ℝ d f) ∧
      (∀ v f, U (HeisenbergStability.Construction.heisenbergOperator real_nondiscrete ψ hc hunit v f) =
        HeisenbergStability.Construction.heisenbergOperator real_nondiscrete ψ hc hunit (FourierCovariance.Construction.fourierPhaseRotation v) (U f)) := by
  obtain ⟨c, hcne, rfl⟩ := RealFourier.Construction.continuous_nontrivial_real_character ψ hc hunit hnontrivial
  let s : ℝ := Real.sqrt (|c| ^ d)
  have hs : 0 < s := Real.sqrt_pos.mpr (pow_pos (abs_pos.mpr hcne) d)
  let U := (realRawFourier d c hcne).trans
    (LinearEquiv.smulOfUnit (Units.mk0 (s : ℂ) (Complex.ofReal_ne_zero.mpr hs.ne')))
  have hU (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) : U f = (s : ℂ) • realRawFourier d c hcne f := rfl
  have hval (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) : (U f).val =
      (s : ℂ) • Local.FunctionsMetaplectic.Construction.fourierIntegral (RealFourier.Construction.realCharacter c) volume f.val := by
    funext x
    change (s : ℂ) * (realRawFourier d c hcne f).val x = _
    rw [realRawFourier_apply]
    rfl
  refine ⟨U, ?_, ?_⟩
  · intro f
    rw [hU, FourierPairing.Construction.l2Energy_smul, realRawFourier_energy]
    have hscale : ‖(s : ℂ)‖ ^ 2 * (|c| ^ d)⁻¹ = 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
      change Real.sqrt (|c| ^ d) ^ 2 * (|c| ^ d)⁻¹ = 1
      rw [Real.sq_sqrt (pow_nonneg (abs_nonneg c) d), mul_inv_cancel₀ (pow_ne_zero d (abs_ne_zero.mpr hcne))]
    rw [← mul_assoc, hscale, one_mul]
  · intro v f
    apply Subtype.ext
    change (U (HeisenbergStability.Construction.heisenbergOperator real_nondiscrete (RealFourier.Construction.realCharacter c) hc hunit v f)).val =
      Local.FunctionsMetaplectic.Construction.heisenbergFunction (RealFourier.Construction.realCharacter c) (FourierCovariance.Construction.fourierPhaseRotation v) (U f).val
    rw [hval, hval]
    change (s : ℂ) • Local.FunctionsMetaplectic.Construction.fourierIntegral (RealFourier.Construction.realCharacter c) volume
      (Local.FunctionsMetaplectic.Construction.heisenbergFunction (RealFourier.Construction.realCharacter c) v f.val) = _
    rw [FourierCovariance.Construction.fourierIntegral_heisenberg, Oscillator.Construction.heisenbergFunction_smul]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.RealFourierUnitary.Construction
