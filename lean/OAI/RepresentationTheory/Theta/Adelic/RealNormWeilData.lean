import OAI.RepresentationTheory.Theta.Adelic.ArchNormRegularizationPhase
import OAI.RepresentationTheory.Theta.Adelic.RealGaussianPhaseComparison
import OAI.RepresentationTheory.Theta.Adelic.RealFieldCharacters
import OAI.RepresentationTheory.Weil.UnitarySplitting.GaussianFormula

/-! # Real Norm Weil Data -/

namespace OAI.RepresentationTheory.Theta.Adelic.RealNormWeilData

noncomputable section

/-! Actual norm Gaussian regularizations for the real field model, with
their Weil constant identified with the native scalar Gaussian product. -/

open _root_.MeasureTheory
open OAI.RepresentationTheory.Weil.UnitarySplitting.GaussianFormula.Construction
open OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalField OAI.RepresentationTheory.Theta.Adelic.RealFieldCharacters OAI.RepresentationTheory.Theta.Adelic.RealGaussianPhaseComparison

theorem real_norm_weil_data (d : ℝ) (hd : d ≠ 0) (hns : ¬ IsSquare d)
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun x : ℝ => ψ x))
    (hu : ∀ x : ℝ, ‖ψ x‖ = 1) (hn : ∃ x : ℝ, ψ x ≠ 1)
    (μE : Measure (QuadraticLocalField.FieldModel ℝ d hns)) [μE.IsAddHaarMeasure] :
    ∃ Γ : ℂ, ∃ hΓ0 : Γ ≠ 0,
      (∀ t : ℝˣ, ∃ Z : ℂ, Z ≠ 0 ∧
        Weil.UnitarySplitting.QuadraticGaussianRegularization.Construction.HasGaussianRegularization μE ψ (fun x => t.val * Algebra.norm ℝ x) Z ∧
        Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase Z = (RealFieldCharacters.realNormCharacter d hd t : ℂ) * Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase Γ) ∧
      (Weil.UnitarySplitting.GaussianFormula.Construction.normWeilConstant (RealFieldCharacters.realNormCharacter d hd) Γ hΓ0 : ℂ) = Weil.AdelicSplitting.Normalization.Construction.quadraticWeilConstant ℝ ψ d := by
  obtain ⟨c, hc0, rfl⟩ := Weil.Local.RealCharacters.Construction.continuous_nontrivial_unitary_real_character ψ hc hu hn
  have ht : 2 * Real.pi * c ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hc0
  have hψ (x : ℝ) : Weil.Local.Gaussian.Construction.realCharacter c x = Complex.exp (Complex.I * (2 * Real.pi * c : ℝ) * (x : ℂ)) := by
    rw [Weil.Local.Gaussian.Construction.realCharacter_apply]
    congr 1
    push_cast
    ring
  obtain ⟨Γ, hΓ0, hΓ, hphase⟩ := ArchNormRegularizationPhase.arch_norm_regularization_phase
    (RingEquiv.refl ℝ) continuous_id (continuous_algebraMap ℝ (QuadraticLocalField.FieldModel ℝ d hns))
    (QuadraticLocalField.model_finrank ℝ d hns) (RealFieldCharacters.realNormCharacter d hd) (RealFieldCharacters.real_model_quadratic_character d hd hns)
    μE (Weil.Local.Gaussian.Construction.realCharacter c) (2 * Real.pi * c) ht hψ
  refine ⟨Γ, hΓ0, hΓ, ?_⟩
  have hh : RealFieldCharacters.realNormCharacter d hd (Units.mk0 (1 / 2 : ℝ) (one_div_ne_zero two_ne_zero)) = 1 := by
    change QuadraticNormCharacter.normSign d _ = 1
    rw [RealNormGaussian.normSign_real d (RealGaussianPhaseComparison.negative_of_nonsquare d hns)]
    norm_num
  change (RealFieldCharacters.realNormCharacter d hd (Units.mk0 (1 / 2 : ℝ) (one_div_ne_zero two_ne_zero)) : ℂ) *
    Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase Γ = _
  rw [hh, Circle.coe_one, one_mul, hphase]
  exact RealGaussianPhaseComparison.complex_norm_phase_eq d (RealGaussianPhaseComparison.negative_of_nonsquare d hns) c hc0

end

end OAI.RepresentationTheory.Theta.Adelic.RealNormWeilData
