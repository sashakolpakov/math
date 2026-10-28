import OAI.RepresentationTheory.Theta.Adelic.FactorScalarAlgebra
import OAI.RepresentationTheory.Theta.Adelic.RealSkewDiagonal
import OAI.RepresentationTheory.Theta.Adelic.RealDeterminantCharacter
import OAI.RepresentationTheory.Theta.Adelic.NormalizedNormGaussian

/-! # Real First Factor Scalar -/

namespace OAI.RepresentationTheory.Theta.Adelic.RealFirstFactorScalar

noncomputable section

/-! The constructed first weighted factor has exactly the corrected
native scalar, with the delta power and skew determinant evaluated. -/

open _root_.MeasureTheory
open OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalField OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldForms OAI.RepresentationTheory.Theta.Adelic.IntrinsicOpenCell.IntrinsicScaledForms
open OAI.RepresentationTheory.Theta.Adelic.RealFieldCharacters OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient OAI.RepresentationTheory.Theta.Adelic.ModelSplittingCharacters

variable (d : ℝ) (hd : d ≠ 0) (hns : ¬ IsSquare d)
variable (ψ : AddChar ℝ ℂ) (hc : Continuous (fun x : ℝ => ψ x))
variable (hu : ∀ x : ℝ, ‖ψ x‖ = 1) (hn : ∃ x : ℝ, ψ x ≠ 1)

include hc hu hn

theorem first_factor_scalar {n m : ℕ}
    (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d))ˣ)
    (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d))ˣ)
    (b : ℝˣ) (hb : QuadraticNormSquareQuotient.scalarUnits d b = (Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd)⁻¹ ^ m * Matrix.GeneralLinearGroup.det K)
    (v : (Matrix (Fin m) (Fin m) (QuadraticLocalField.FieldModel ℝ d hns))ˣ) (a : Fin m → ℝˣ)
    (hdiag : Weil.UnitarySplitting.DualPair.Construction.adjointMatrix (QuadraticLocalField.conjugation ℝ d hns) v.val * (-(QuadraticFieldForms.modelForm d hns K.val)) * v.val =
      (QuadraticLocalField.algebraEquiv ℝ d hns).symm (Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd).val • Weil.UnitarySplitting.TensorUnitary.Construction.multiplicityForm a)
    (χ : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d)ˣ →ₜ* Circle)
    (Q : Matrix (Fin n) (Fin n) (QuadraticLocalField.FieldModel ℝ d hns))
    (hQ : Q = QuadraticFieldForms.modelForm d hns (IntrinsicOpenCell.IntrinsicScaledForms.scaledUnit d (Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd) H).val)
    (g : Weil.UnitarySplitting.DualPair.Construction.unitaryGroup (QuadraticLocalField.conjugation ℝ d hns) Q)
    (u : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d))ˣ)
    (hDiff : g.val.val - 1 = QuadraticFieldForms.modelForm d hns u.val)
    (Γ : ℂ) (hΓ0 : Γ ≠ 0)
    (hnorm : (Weil.UnitarySplitting.GaussianFormula.Construction.normWeilConstant (RealFieldCharacters.realNormCharacter d hd) Γ hΓ0 : ℂ) = Weil.AdelicSplitting.Normalization.Construction.quadraticWeilConstant ℝ ψ d) :
    let ω := RealFieldCharacters.realNormCharacter d hd
    (((Weil.UnitarySplitting.WeightedTensorGaussian.Construction.tensorWeilConstant ω Γ hΓ0 a n *
      Weil.UnitarySplitting.GenericDeterminantCharacter.Construction.genericDeterminantCharacter (QuadraticLocalField.conjugation ℝ d hns) Q ((χ.comp (RealFieldCharacters.realNativeUnits d hns))⁻¹) g)⁻¹ : Circle) : ℂ) =
        (Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant ℝ ψ d)⁻¹ ^ (n * m) * (QuadraticNormCharacter.normSign d b : ℂ) ^ n *
          (χ ((Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd) ^ n * Matrix.GeneralLinearGroup.det H * Matrix.GeneralLinearGroup.det u) : ℂ) := by
  dsimp only
  let ω := RealFieldCharacters.realNormCharacter d hd
  let κ := Weil.UnitarySplitting.GenericDeterminantCharacter.Construction.genericDeterminantCharacter (QuadraticLocalField.conjugation ℝ d hns) Q ((χ.comp (RealFieldCharacters.realNativeUnits d hns))⁻¹) g
  let χg := χ ((Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd) ^ n * Matrix.GeneralLinearGroup.det H * Matrix.GeneralLinearGroup.det u)
  have hκ : κ⁻¹ = χg := by
    have h := RealDeterminantCharacter.inverse_determinant_character_of_form d hns
      (IntrinsicOpenCell.IntrinsicScaledForms.scaledUnit d (Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd) H) u χ Q hQ g hDiff
    simpa only [IntrinsicOpenCell.IntrinsicScaledForms.scaledUnit_det, Fintype.card_fin] using h
  have hwt : ω (∏ i, a i) = ω (-1) ^ m * ω b :=
    RealSkewDiagonal.skew_diagonal_character d hd hns K b hb v a hdiag
  have hcircle : (Weil.UnitarySplitting.WeightedTensorGaussian.Construction.tensorWeilConstant ω Γ hΓ0 a n * κ)⁻¹ =
      (ω (-1) * Weil.UnitarySplitting.GaussianFormula.Construction.normWeilConstant ω Γ hΓ0)⁻¹ ^ (n * m) * (ω b) ^ n * χg := by
    rw [Weil.UnitarySplitting.WeightedTensorGaussian.Construction.tensorWeilConstant, hwt]
    exact FactorScalarAlgebra.inverse_left_scalar n m _ _ _ κ χg
      (ModelSplittingCharacters.normSign_inv_self d (-1)) (ModelSplittingCharacters.normSign_inv_self d b) hκ
  change (Weil.UnitarySplitting.GaussianFormula.Construction.normWeilConstant ω Γ hΓ0 : ℂ) = Weil.AdelicSplitting.Normalization.Construction.quadraticWeilConstant ℝ ψ d at hnorm
  have h := congrArg (fun z : Circle => (z : ℂ)) hcircle
  simp only [Circle.coe_mul, Circle.coe_pow, Circle.coe_inv, hnorm] at h
  rw [NormalizedNormGaussian.schrodingerWeilConstant_sign Weil.UnitarySplitting.RealFourierUnitary.Construction.real_nondiscrete ψ hc hu hn d hd]
  exact h

end

end OAI.RepresentationTheory.Theta.Adelic.RealFirstFactorScalar
