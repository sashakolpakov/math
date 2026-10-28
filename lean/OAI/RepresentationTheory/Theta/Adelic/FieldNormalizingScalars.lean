import OAI.RepresentationTheory.Theta.Adelic.FieldCharacterTransport
import OAI.RepresentationTheory.Theta.Adelic.RealFieldWeilConstant

/-! # Field Normalizing Scalars -/

namespace OAI.RepresentationTheory.Theta.Adelic.FieldNormalizingScalars

noncomputable section

/-! Both explicit native normalizing scalars are unchanged by passage
to real field coordinates. -/

open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter OAI.RepresentationTheory.Theta.Adelic.QuadraticNormTransport
open OAI.RepresentationTheory.Theta.Adelic.FieldCharacterTransport.Unitary OAI.RepresentationTheory.Theta.Adelic.FieldCharacterTransport OAI.RepresentationTheory.Theta.Adelic.RealFieldWeilConstant

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [MeasurableSpace k] [BorelSpace k]
variable (hArch : ¬ ∀ j : ℕ, ‖(j : k)‖ ≤ 1)
variable (e : k ≃+* ℝ) (he : Continuous e) (hi : Continuous e.symm)
variable (ψ : AddChar k ℂ) (hc : Continuous (fun x : k => ψ x))
variable (hu : ∀ x : k, ‖ψ x‖ = 1) (hn : ∃ x : k, ψ x ≠ 1)
variable (d : k) (hd : d ≠ 0) (n m : ℕ)

include hArch hc hu hn

theorem first_scalar_field
    (H u : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (b : kˣ) (χ : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ →ₜ* Circle) :
    (Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant k ψ d)⁻¹ ^ (n * m) * (QuadraticNormCharacter.normSign d b : ℂ) ^ n *
      (χ ((Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd) ^ n * Matrix.GeneralLinearGroup.det H * Matrix.GeneralLinearGroup.det u) : ℂ) =
    (Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant ℝ (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) (e d))⁻¹ ^ (n * m) *
      (QuadraticNormCharacter.normSign (e d) (Units.map e.toMonoidHom b) : ℂ) ^ n *
      (FieldCharacterTransport.fieldMultiplicativeCharacter e he hi d χ
        ((Weil.AdelicSplitting.Normalization.Construction.deltaUnit (e d) ((map_ne_zero e).mpr hd)) ^ n *
          Matrix.GeneralLinearGroup.det (FieldCharacterTransport.Unitary.fieldFormUnit e d H) * Matrix.GeneralLinearGroup.det (FieldCharacterTransport.Unitary.fieldFormUnit e d u)) : ℂ) := by
  have ha : FieldCharacterTransport.Unitary.fieldQuadraticUnits e d
      ((Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd) ^ n * Matrix.GeneralLinearGroup.det H * Matrix.GeneralLinearGroup.det u) =
      (Weil.AdelicSplitting.Normalization.Construction.deltaUnit (e d) ((map_ne_zero e).mpr hd)) ^ n *
        Matrix.GeneralLinearGroup.det (FieldCharacterTransport.Unitary.fieldFormUnit e d H) * Matrix.GeneralLinearGroup.det (FieldCharacterTransport.Unitary.fieldFormUnit e d u) := by
    rw [map_mul, map_mul, map_pow, FieldCharacterTransport.Unitary.fieldQuadraticUnits_delta, ← FieldCharacterTransport.Unitary.fieldFormUnit_det, ← FieldCharacterTransport.Unitary.fieldFormUnit_det]
  rw [← ha, FieldCharacterTransport.fieldMultiplicativeCharacter_apply, QuadraticNormTransport.normSign_map,
    RealFieldWeilConstant.schrodingerWeilConstant_field hArch e he hi ψ hc hu hn d hd]

include hd in
theorem second_scalar_field
    (K u : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (b : kˣ) (χ : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ →ₜ* Circle) :
    (Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant k ψ d)⁻¹ ^ (n * m) * (QuadraticNormCharacter.normSign d b : ℂ) ^ m *
      (χ (Matrix.GeneralLinearGroup.det K * Matrix.GeneralLinearGroup.det u) : ℂ) =
    (Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant ℝ (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) (e d))⁻¹ ^ (n * m) *
      (QuadraticNormCharacter.normSign (e d) (Units.map e.toMonoidHom b) : ℂ) ^ m *
      (FieldCharacterTransport.fieldMultiplicativeCharacter e he hi d χ
        (Matrix.GeneralLinearGroup.det (FieldCharacterTransport.Unitary.fieldFormUnit e d K) * Matrix.GeneralLinearGroup.det (FieldCharacterTransport.Unitary.fieldFormUnit e d u)) : ℂ) := by
  have ha : FieldCharacterTransport.Unitary.fieldQuadraticUnits e d (Matrix.GeneralLinearGroup.det K * Matrix.GeneralLinearGroup.det u) =
      Matrix.GeneralLinearGroup.det (FieldCharacterTransport.Unitary.fieldFormUnit e d K) * Matrix.GeneralLinearGroup.det (FieldCharacterTransport.Unitary.fieldFormUnit e d u) := by
    rw [map_mul, ← FieldCharacterTransport.Unitary.fieldFormUnit_det, ← FieldCharacterTransport.Unitary.fieldFormUnit_det]
  rw [← ha, FieldCharacterTransport.fieldMultiplicativeCharacter_apply, QuadraticNormTransport.normSign_map,
    RealFieldWeilConstant.schrodingerWeilConstant_field hArch e he hi ψ hc hu hn d hd]

end

end OAI.RepresentationTheory.Theta.Adelic.FieldNormalizingScalars
