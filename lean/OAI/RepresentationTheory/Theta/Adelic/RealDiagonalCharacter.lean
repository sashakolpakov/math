import OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldForms
import OAI.RepresentationTheory.Theta.Adelic.RealFieldCharacters
import OAI.RepresentationTheory.Weil.UnitarySplitting.HermitianGaussianDiscriminant
import OAI.RepresentationTheory.Weil.UnitarySplitting.TensorUnitary

/-! # Real Diagonal Character -/

namespace OAI.RepresentationTheory.Theta.Adelic.RealDiagonalCharacter

noncomputable section

/-! Evaluate the norm character of diagonal multiplicities by the actual
native scalar determinant; the change-of-basis norm factor is eliminated. -/

open OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalField OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldForms OAI.RepresentationTheory.Theta.Adelic.RealFieldCharacters
open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient

variable (d : ℝ) (hd : d ≠ 0) (hns : ¬ IsSquare d) {r : ℕ}

include hd in
theorem diagonal_character
    (A : (Matrix (Fin r) (Fin r) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d))ˣ) (b : ℝˣ)
    (hb : QuadraticNormSquareQuotient.scalarUnits d b = Matrix.GeneralLinearGroup.det A)
    (u : (Matrix (Fin r) (Fin r) (QuadraticLocalField.FieldModel ℝ d hns))ˣ) (a : Fin r → ℝˣ)
    (hdiag : Weil.UnitarySplitting.DualPair.Construction.adjointMatrix (QuadraticLocalField.conjugation ℝ d hns) u.val * QuadraticFieldForms.modelForm d hns A.val * u.val = Weil.UnitarySplitting.TensorUnitary.Construction.multiplicityForm a) :
    QuadraticNormCharacter.normSign d (∏ i, a i) = QuadraticNormCharacter.normSign d b := by
  have hbase : algebraMap ℝ (QuadraticLocalField.FieldModel ℝ d hns) b.val = (QuadraticFieldForms.modelForm d hns A.val).det := by
    apply (QuadraticLocalField.algebraEquiv ℝ d hns).injective
    rw [AlgEquiv.commutes]
    change algebraMap ℝ (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d) b.val =
      (QuadraticLocalField.algebraEquiv ℝ d hns) (((QuadraticLocalField.algebraEquiv ℝ d hns).symm.toRingHom.mapMatrix A.val).det)
    rw [← RingHom.map_det]
    change algebraMap ℝ (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d) b.val = (QuadraticLocalField.algebraEquiv ℝ d hns) ((QuadraticLocalField.algebraEquiv ℝ d hns).symm A.val.det)
    rw [AlgEquiv.apply_symm_apply]
    exact congrArg Units.val hb
  exact Weil.UnitarySplitting.HermitianGaussianDiscriminant.Construction.hermitianDiagonal_discriminant_character (QuadraticLocalField.model_finrank ℝ d hns) (QuadraticLocalField.conjugation ℝ d hns)
    (QuadraticLocalField.conjugation_nontrivial ℝ d hns) (RealFieldCharacters.realNormCharacter d hd)
    (RealFieldCharacters.real_model_quadratic_character d hd hns) (QuadraticFieldForms.modelForm d hns A.val) u a b hbase hdiag

end

end OAI.RepresentationTheory.Theta.Adelic.RealDiagonalCharacter
