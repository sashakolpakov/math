import OAI.RepresentationTheory.Theta.Adelic.IntrinsicDeterminantCharacter
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeightedTensorGaussian

/-! # Factor Scalar Algebra -/

namespace OAI.RepresentationTheory.Theta.Adelic.FactorScalarAlgebra

noncomputable section

/-! The two explicit scalar identities used to compare weighted Gaussian
splittings with the corrected first and second unitary factors. -/

theorem inverse_left_scalar (n m : ℕ) (c ε b κ χ : Circle)
    (hε : ε⁻¹ = ε) (hb : b⁻¹ = b) (hκ : κ⁻¹ = χ) :
    (c ^ (n * m) * (ε ^ m * b) ^ n * κ)⁻¹ =
      (ε * c)⁻¹ ^ (n * m) * b ^ n * χ := by
  rw [mul_inv_rev, hκ]
  simp only [mul_inv_rev, ← inv_pow, hε, hb, mul_pow, ← pow_mul, Nat.mul_comm]
  simp only [mul_assoc, mul_left_comm, mul_comm]

theorem inverse_right_scalar (n m : ℕ) (c ε b κ χ : Circle)
    (hε : ε⁻¹ = ε) (hb : b⁻¹ = b) (hκ : κ⁻¹ = ε ^ (n * m) * χ) :
    (c ^ (m * n) * b ^ m * κ)⁻¹ =
      (ε * c)⁻¹ ^ (n * m) * b ^ m * χ := by
  rw [mul_inv_rev, hκ]
  simp only [mul_inv_rev, ← inv_pow, hε, hb, mul_pow, Nat.mul_comm]
  simp only [mul_assoc, mul_left_comm, mul_comm]

open OAI.RepresentationTheory.Weil.UnitarySplitting.WeightedTensorGaussian.Construction
open OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalField OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldForms OAI.RepresentationTheory.Theta.Adelic.ModelSplittingCharacters

theorem inverse_determinant_character_of_form
    {k : Type} [NontriviallyNormedField k] [CompleteSpace k] [IsUltrametricDist k]
    (d : k) (hns : ¬ IsSquare d) {I : Type} [Fintype I] [DecidableEq I]
    (A u : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (χ : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ →ₜ* Circle)
    (Q : Matrix I I (QuadraticLocalField.FieldModel k d hns)) (hQ : Q = QuadraticFieldForms.modelForm d hns A.val)
    (g : Weil.UnitarySplitting.DualPair.Construction.unitaryGroup (QuadraticLocalField.conjugation k d hns) Q)
    (hu : g.val.val - 1 = QuadraticFieldForms.modelForm d hns u.val) :
    (Weil.UnitarySplitting.GenericDeterminantCharacter.Construction.genericDeterminantCharacter (QuadraticLocalField.conjugation k d hns) Q ((χ.comp (ModelSplittingCharacters.nativeUnits d hns))⁻¹) g)⁻¹ =
      χ (Matrix.GeneralLinearGroup.det A * Matrix.GeneralLinearGroup.det u) := by
  subst Q
  exact IntrinsicDeterminantCharacter.Intrinsic.inverse_determinant_character d hns A u χ g hu

end

end OAI.RepresentationTheory.Theta.Adelic.FactorScalarAlgebra
