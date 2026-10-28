import OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldForms
import OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalCharacter
import OAI.RepresentationTheory.Weil.UnitarySplitting.HermitianGaussianDiscriminant
import OAI.RepresentationTheory.Weil.UnitarySplitting.TensorUnitary

/-! # Intrinsic Diagonal Character -/

namespace OAI.RepresentationTheory.Theta.Adelic.IntrinsicDiagonalCharacter.Intrinsic

noncomputable section

/-! Evaluate the norm character of diagonal multiplicities by the actual
native scalar determinant; the change-of-basis norm factor is eliminated. -/

open OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalField OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldForms OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalCharacter
open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient

variable {k : Type} [NontriviallyNormedField k] [CompleteSpace k] [LocallyCompactSpace k]
variable [IsUltrametricDist k] [CharZero k]
variable (d : k) (hd : d ≠ 0) (hns : ¬ IsSquare d) (hnd : ¬ DiscreteTopology k) {r : ℕ}

include hd hnd in
theorem diagonal_character
    (A : (Matrix (Fin r) (Fin r) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (b : kˣ)
    (hb : QuadraticNormSquareQuotient.scalarUnits d b = Matrix.GeneralLinearGroup.det A)
    (u : (Matrix (Fin r) (Fin r) (QuadraticLocalField.FieldModel k d hns))ˣ) (a : Fin r → kˣ)
    (hdiag : Weil.UnitarySplitting.DualPair.Construction.adjointMatrix (QuadraticLocalField.conjugation k d hns) u.val * QuadraticFieldForms.modelForm d hns A.val * u.val = Weil.UnitarySplitting.TensorUnitary.Construction.multiplicityForm a) :
    QuadraticNormCharacter.normSign d (∏ i, a i) = QuadraticNormCharacter.normSign d b := by
  have hbase : algebraMap k (QuadraticLocalField.FieldModel k d hns) b.val = (QuadraticFieldForms.modelForm d hns A.val).det := by
    apply (QuadraticLocalField.algebraEquiv k d hns).injective
    rw [AlgEquiv.commutes]
    change algebraMap k (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) b.val =
      (QuadraticLocalField.algebraEquiv k d hns) (((QuadraticLocalField.algebraEquiv k d hns).symm.toRingHom.mapMatrix A.val).det)
    rw [← RingHom.map_det]
    change algebraMap k (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) b.val = (QuadraticLocalField.algebraEquiv k d hns) ((QuadraticLocalField.algebraEquiv k d hns).symm A.val.det)
    rw [AlgEquiv.apply_symm_apply]
    exact congrArg Units.val hb
  exact Weil.UnitarySplitting.HermitianGaussianDiscriminant.Construction.hermitianDiagonal_discriminant_character (QuadraticLocalField.model_finrank k d hns) (QuadraticLocalField.conjugation k d hns)
    (QuadraticLocalField.conjugation_nontrivial k d hns) (QuadraticNormCharacter.nonarchimedeanNormCharacter d hd hnd)
    (QuadraticLocalCharacter.model_quadratic_character d hd hns hnd) (QuadraticFieldForms.modelForm d hns A.val) u a b hbase hdiag

end

end OAI.RepresentationTheory.Theta.Adelic.IntrinsicDiagonalCharacter.Intrinsic
