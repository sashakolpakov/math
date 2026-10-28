import OAI.RepresentationTheory.Theta.Adelic.LocalNormGaussian
import OAI.RepresentationTheory.Theta.Adelic.LocalNormCharacter
import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization

/-! # Normalized Norm Gaussian -/

namespace OAI.RepresentationTheory.Theta.Adelic.NormalizedNormGaussian

noncomputable section

/-! The norm Gaussian formula with unit reference coefficient, and the
exact sign relating UnitarySplitting's Weil constant to the corrected AdelicSplitting constant. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization.Construction OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [MeasurableSpace k] [BorelSpace k]
variable (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ)
variable (hc : Continuous (fun x : k => ψ x)) (hu : ∀ x : k, ‖ψ x‖ = 1)
variable (hn : ∃ x : k, ψ x ≠ 1) (d : k) (hd : d ≠ 0)

include hc hu hn hd hnd

theorem norm_character_gaussian_identity (a : kˣ) :
    (QuadraticNormCharacter.normSign d a : ℂ) * Weil.AdelicSplitting.Normalization.Construction.quadraticWeilConstant k ψ d =
      Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val * Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (-d * a.val) := by
  let t : kˣ := Units.mk0 (1 / 2 : k) (one_div_ne_zero two_ne_zero)
  have ht2 : (2 : k) * t.val = 1 := by dsimp [t]; field_simp
  have htd : -2 * d * t.val = -d := by dsimp [t]; field_simp
  have hat : (2 : k) * (a * t).val = a.val := by change 2 * (a.val * (1 / 2)) = a.val; field_simp
  have had : -2 * d * (a * t).val = -d * a.val := by
    change -2 * d * (a.val * (1 / 2)) = -d * a.val
    field_simp
  have ht := LocalNormGaussian.norm_character_gaussian_identity hnd ψ hc hu hn d hd t
  have ha := LocalNormGaussian.norm_character_gaussian_identity hnd ψ hc hu hn d hd (a * t)
  rw [ht2, htd] at ht
  rw [hat, had, LocalNormCharacter.normSign_mul hnd d hd a t, Circle.coe_mul,
    mul_assoc, ht] at ha
  exact ha

theorem schrodingerWeilConstant_sign :
    Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant k ψ d =
      (QuadraticNormCharacter.normSign d (-1) : ℂ) * Weil.AdelicSplitting.Normalization.Construction.quadraticWeilConstant k ψ d := by
  have h := norm_character_gaussian_identity hnd ψ hc hu hn d hd (-1)
  simpa only [Units.val_neg, Units.val_one, neg_mul_neg, mul_one,
    Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant] using h.symm

end

end OAI.RepresentationTheory.Theta.Adelic.NormalizedNormGaussian
