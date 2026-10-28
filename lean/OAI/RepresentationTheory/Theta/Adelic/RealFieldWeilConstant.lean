import OAI.RepresentationTheory.Weil.Local.RealFieldEq
import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization

/-! # Real Field Weil Constant -/

namespace OAI.RepresentationTheory.Theta.Adelic.RealFieldWeilConstant

noncomputable section

/-! Exact transport of the native Weil constants to real coordinates,
using the actual oscillatory Gaussian limits and Haar normalization. -/

open OAI.RepresentationTheory.Weil.Local.RealFieldEq.Construction OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization.Construction

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [MeasurableSpace k] [BorelSpace k]
variable (hArch : ¬ ∀ m : ℕ, ‖(m : k)‖ ≤ 1)
variable (e : k ≃+* ℝ) (he : Continuous e) (hi : Continuous e.symm)
variable (ψ : AddChar k ℂ) (hc : Continuous (fun x : k => ψ x))
variable (hu : ∀ x : k, ‖ψ x‖ = 1) (hn : ∃ x : k, ψ x ≠ 1)

include hArch he hi hc hu hn

theorem schrodingerWeilConstant_field (d : k) (hd : d ≠ 0) :
    Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant k ψ d =
      Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant ℝ (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) (e d) := by
  have h := Weil.Local.RealFieldEq.Construction.realField_gaussian_normalization hArch e he hi ψ hc hu hn
  rw [Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant, Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant,
    (h (-1) (neg_ne_zero.mpr one_ne_zero)).2, (h d hd).2, map_neg, map_one]

theorem quadraticWeilConstant_field (d : k) (hd : d ≠ 0) :
    Weil.AdelicSplitting.Normalization.Construction.quadraticWeilConstant k ψ d = Weil.AdelicSplitting.Normalization.Construction.quadraticWeilConstant ℝ (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) (e d) := by
  have h := Weil.Local.RealFieldEq.Construction.realField_gaussian_normalization hArch e he hi ψ hc hu hn
  rw [Weil.AdelicSplitting.Normalization.Construction.quadraticWeilConstant, Weil.AdelicSplitting.Normalization.Construction.quadraticWeilConstant,
    (h 1 one_ne_zero).2, (h (-d) (neg_ne_zero.mpr hd)).2, map_one, map_neg]

end

end OAI.RepresentationTheory.Theta.Adelic.RealFieldWeilConstant
