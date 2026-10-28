import OAI.RepresentationTheory.Theta.Adelic.RealFieldCharacters
import OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldForms
import OAI.RepresentationTheory.Weil.UnitarySplitting.GenericDeterminantCharacter

/-! # Real Determinant Character -/

namespace OAI.RepresentationTheory.Theta.Adelic.RealDeterminantCharacter

noncomputable section

/-! Evaluate the inverse determinant-character correction in the native
quadratic algebra, for the actual form and an invertible open-cell difference. -/

open OAI.RepresentationTheory.Weil.UnitarySplitting.GenericDeterminantCharacter.Construction
open OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalField OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldForms OAI.RepresentationTheory.Theta.Adelic.RealFieldCharacters

variable (d : ℝ) (hns : ¬ IsSquare d) {I : Type} [Fintype I] [DecidableEq I]

theorem inverse_determinant_character
    (A u : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d))ˣ) (χ : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d)ˣ →ₜ* Circle)
    (g : Weil.UnitarySplitting.DualPair.Construction.unitaryGroup (QuadraticLocalField.conjugation ℝ d hns) (QuadraticFieldForms.modelForm d hns A.val))
    (hu : g.val.val - 1 = QuadraticFieldForms.modelForm d hns u.val) :
    (Weil.UnitarySplitting.GenericDeterminantCharacter.Construction.genericDeterminantCharacter (QuadraticLocalField.conjugation ℝ d hns) (QuadraticFieldForms.modelForm d hns A.val)
      ((χ.comp (RealFieldCharacters.realNativeUnits d hns))⁻¹) g)⁻¹ =
        χ (Matrix.GeneralLinearGroup.det A * Matrix.GeneralLinearGroup.det u) := by
  let v := Matrix.GeneralLinearGroup.det A * Matrix.GeneralLinearGroup.det u
  let w : (QuadraticLocalField.FieldModel ℝ d hns)ˣ := Units.map (QuadraticLocalField.algebraEquiv ℝ d hns).symm.toMonoidHom v
  have hval : (Weil.UnitarySplitting.TracePairing.Construction.unitaryDifferenceForm (QuadraticLocalField.conjugation ℝ d hns) (QuadraticFieldForms.modelForm d hns A.val) g).det = w.val := by
    rw [Weil.UnitarySplitting.TensorUnitary.Construction.unitaryDifferenceForm_det, hu]
    change ((QuadraticLocalField.algebraEquiv ℝ d hns).symm.toRingHom.mapMatrix A.val).det *
      ((QuadraticLocalField.algebraEquiv ℝ d hns).symm.toRingHom.mapMatrix u.val).det =
      (QuadraticLocalField.algebraEquiv ℝ d hns).symm (A.val.det * u.val.det)
    rw [← RingHom.map_det, ← RingHom.map_det, map_mul]
    rfl
  have hn : (Weil.UnitarySplitting.TracePairing.Construction.unitaryDifferenceForm (QuadraticLocalField.conjugation ℝ d hns) (QuadraticFieldForms.modelForm d hns A.val) g).det ≠ 0 :=
    hval.trans_ne w.ne_zero
  rw [Weil.UnitarySplitting.GenericDeterminantCharacter.Construction.genericDeterminantCharacter, Weil.UnitarySplitting.GenericDeterminantCharacter.Construction.unitCharacterValue_apply _ _ hn]
  have hw : Units.mk0 (Weil.UnitarySplitting.TracePairing.Construction.unitaryDifferenceForm (QuadraticLocalField.conjugation ℝ d hns) (QuadraticFieldForms.modelForm d hns A.val) g).det hn = w :=
    Units.ext hval
  rw [hw]
  change ((χ (RealFieldCharacters.realNativeUnits d hns w))⁻¹)⁻¹ = χ v
  rw [inv_inv]
  congr 1

theorem inverse_determinant_character_of_form
    (A u : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d))ˣ) (χ : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d)ˣ →ₜ* Circle)
    (Q : Matrix I I (QuadraticLocalField.FieldModel ℝ d hns)) (hQ : Q = QuadraticFieldForms.modelForm d hns A.val)
    (g : Weil.UnitarySplitting.DualPair.Construction.unitaryGroup (QuadraticLocalField.conjugation ℝ d hns) Q)
    (hu : g.val.val - 1 = QuadraticFieldForms.modelForm d hns u.val) :
    (Weil.UnitarySplitting.GenericDeterminantCharacter.Construction.genericDeterminantCharacter (QuadraticLocalField.conjugation ℝ d hns) Q
      ((χ.comp (RealFieldCharacters.realNativeUnits d hns))⁻¹) g)⁻¹ =
        χ (Matrix.GeneralLinearGroup.det A * Matrix.GeneralLinearGroup.det u) := by
  subst Q
  exact inverse_determinant_character d hns A u χ g hu

end

end OAI.RepresentationTheory.Theta.Adelic.RealDeterminantCharacter
