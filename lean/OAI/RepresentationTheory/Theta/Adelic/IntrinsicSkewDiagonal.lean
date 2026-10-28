import OAI.RepresentationTheory.Theta.Adelic.IntrinsicOpenCell
import OAI.RepresentationTheory.Theta.Adelic.IntrinsicDiagonalCharacter

/-! # Intrinsic Skew Diagonal -/

namespace OAI.RepresentationTheory.Theta.Adelic.IntrinsicSkewDiagonal.Intrinsic

noncomputable section

/-! The diagonal multiplicities of -K give the prescribed scalar
determinant of K, including the exact power of the norm character at -1. -/

open OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalField OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldForms OAI.RepresentationTheory.Theta.Adelic.IntrinsicOpenCell.IntrinsicScaledForms
open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient

variable {k : Type} [NontriviallyNormedField k] [CompleteSpace k] [LocallyCompactSpace k]
variable [IsUltrametricDist k] [CharZero k]
variable (d : k) (hd : d ≠ 0) (hns : ¬ IsSquare d) (hnd : ¬ DiscreteTopology k) {m : ℕ}

include hnd in
theorem skew_diagonal_character
    (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (b : kˣ)
    (hb : QuadraticNormSquareQuotient.scalarUnits d b = (Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd)⁻¹ ^ m * Matrix.GeneralLinearGroup.det K)
    (u : (Matrix (Fin m) (Fin m) (QuadraticLocalField.FieldModel k d hns))ˣ) (a : Fin m → kˣ)
    (hdiag : Weil.UnitarySplitting.DualPair.Construction.adjointMatrix (QuadraticLocalField.conjugation k d hns) u.val * (-(QuadraticFieldForms.modelForm d hns K.val)) * u.val =
      (QuadraticLocalField.algebraEquiv k d hns).symm (Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd).val • Weil.UnitarySplitting.TensorUnitary.Construction.multiplicityForm a) :
    QuadraticNormCharacter.normSign d (∏ i, a i) = QuadraticNormCharacter.normSign d (-1) ^ m * QuadraticNormCharacter.normSign d b := by
  let A := IntrinsicOpenCell.IntrinsicScaledForms.scaledUnit d (-1) K
  let B := IntrinsicOpenCell.IntrinsicScaledForms.scaledUnit d (Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd)⁻¹ A
  let b' := (-1 : kˣ) ^ m * b
  have hminus : QuadraticNormSquareQuotient.scalarUnits d (-1 : kˣ) = -1 := by
    apply Units.ext
    ext <;> simp [QuadraticNormSquareQuotient.scalarUnits]
  have hb' : QuadraticNormSquareQuotient.scalarUnits d b' = Matrix.GeneralLinearGroup.det B := by
    change QuadraticNormSquareQuotient.scalarUnits d ((-1) ^ m * b) =
      Matrix.GeneralLinearGroup.det (IntrinsicOpenCell.IntrinsicScaledForms.scaledUnit d (Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd)⁻¹ (IntrinsicOpenCell.IntrinsicScaledForms.scaledUnit d (-1) K))
    rw [map_mul, map_pow, hminus, hb, IntrinsicOpenCell.IntrinsicScaledForms.scaledUnit_det, IntrinsicOpenCell.IntrinsicScaledForms.scaledUnit_det, Fintype.card_fin]
    ac_rfl
  let z := (QuadraticLocalField.algebraEquiv k d hns).symm (Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd).val
  have hz : z ≠ 0 := by
    intro hz0
    exact (Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd).ne_zero ((QuadraticLocalField.algebraEquiv k d hns).symm.injective
      (hz0.trans (map_zero _).symm))
  have hi : (QuadraticLocalField.algebraEquiv k d hns).symm ((Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd)⁻¹).val = z⁻¹ :=
    map_units_inv (QuadraticLocalField.algebraEquiv k d hns).symm (Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd)
  have hm : (QuadraticLocalField.algebraEquiv k d hns).symm (-1 : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ).val = (-1 : QuadraticLocalField.FieldModel k d hns) := by
    change (QuadraticLocalField.algebraEquiv k d hns).symm (-1) = -1
    rw [map_neg, map_one]
  have hB : QuadraticFieldForms.modelForm d hns B.val = z⁻¹ • (-(QuadraticFieldForms.modelForm d hns K.val)) := by
    change QuadraticFieldForms.modelForm d hns (IntrinsicOpenCell.IntrinsicScaledForms.scaledUnit d (Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd)⁻¹ (IntrinsicOpenCell.IntrinsicScaledForms.scaledUnit d (-1) K)).val = _
    rw [IntrinsicOpenCell.IntrinsicScaledForms.modelForm_scaled, IntrinsicOpenCell.IntrinsicScaledForms.modelForm_scaled, hi, hm, neg_one_smul]
  have hdiagB : Weil.UnitarySplitting.DualPair.Construction.adjointMatrix (QuadraticLocalField.conjugation k d hns) u.val * QuadraticFieldForms.modelForm d hns B.val * u.val = Weil.UnitarySplitting.TensorUnitary.Construction.multiplicityForm a := by
    rw [hB, mul_smul_comm, smul_mul_assoc, hdiag]
    change z⁻¹ • (z • Weil.UnitarySplitting.TensorUnitary.Construction.multiplicityForm a) = Weil.UnitarySplitting.TensorUnitary.Construction.multiplicityForm a
    rw [smul_smul, inv_mul_cancel₀ hz, one_smul]
  have h := IntrinsicDiagonalCharacter.Intrinsic.diagonal_character d hd hns hnd B b' hb' u a hdiagB
  let ω := QuadraticNormCharacter.nonarchimedeanNormCharacter d hd hnd
  change ω (∏ i, a i) = ω b' at h
  change ω (∏ i, a i) = ω (-1) ^ m * ω b
  rw [h]
  exact (map_mul ω ((-1) ^ m) b).trans (congrArg (fun t : Circle => t * ω b) (map_pow ω (-1) m))

end

end OAI.RepresentationTheory.Theta.Adelic.IntrinsicSkewDiagonal.Intrinsic
