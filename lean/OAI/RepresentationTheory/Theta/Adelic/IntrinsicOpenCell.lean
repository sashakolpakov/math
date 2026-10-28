import OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldFrame
import OAI.RepresentationTheory.Theta.Adelic.FixedDeterminant
import OAI.RepresentationTheory.Weil.UnitarySplitting.FormScaling

/-! # Intrinsic Open Cell -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.IntrinsicOpenCell.IntrinsicScaledForms

/-! Scalar changes of the native form matrices, their determinants, and
their exact quadratic-field-model realizations. -/

open OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalField OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldForms OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldFrame

variable {k : Type} [Field k] (d : k) (hns : ¬ IsSquare d)
variable {I : Type} [Fintype I] [DecidableEq I]

def scaledUnit (z : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ) (A : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) :
    (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ := Matrix.GeneralLinearGroup.scalar I z * A

theorem scaledUnit_val (z : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ) (A : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) :
    (scaledUnit d z A).val = z.val • A.val := by
  change Matrix.scalar I z.val * A.val = z.val • A.val
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

theorem scaledUnit_det (z : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ) (A : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) :
    Matrix.GeneralLinearGroup.det (scaledUnit d z A) = z ^ Fintype.card I * Matrix.GeneralLinearGroup.det A := by
  rw [scaledUnit, map_mul, Matrix.GeneralLinearGroup.det_scalar]

theorem modelForm_scaled (z : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ) (A : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) :
    QuadraticFieldForms.modelForm d hns (scaledUnit d z A).val =
      (QuadraticLocalField.algebraEquiv k d hns).symm z.val • QuadraticFieldForms.modelForm d hns A.val := by
  rw [scaledUnit_val]
  ext i j
  exact (QuadraticLocalField.algebraEquiv k d hns).symm.map_mul z.val (A.val i j)

omit [Fintype I] [DecidableEq I] in
theorem modelForm_neg (A : Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) :
    QuadraticFieldForms.modelForm d hns (-A) = -(QuadraticFieldForms.modelForm d hns A) := by
  ext i j
  exact (QuadraticLocalField.algebraEquiv k d hns).symm.map_neg (A i j)

omit [Fintype I] [DecidableEq I] in
theorem modelForm_hermitian (A : Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) (hA : A.conjTranspose = A) :
    Weil.UnitarySplitting.DualPair.Construction.adjointMatrix (QuadraticLocalField.conjugation k d hns) (QuadraticFieldForms.modelForm d hns A) = QuadraticFieldForms.modelForm d hns A := by
  rw [QuadraticFieldForms.modelForm_adjoint, hA]

omit [Fintype I] [DecidableEq I] in
theorem modelForm_skew (A : Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) (hA : A.conjTranspose = -A) :
    Weil.UnitarySplitting.DualPair.Construction.adjointMatrix (QuadraticLocalField.conjugation k d hns) (QuadraticFieldForms.modelForm d hns A) = -(QuadraticFieldForms.modelForm d hns A) := by
  rw [QuadraticFieldForms.modelForm_adjoint, hA, modelForm_neg]

theorem model_delta_antifixed (hd : d ≠ 0) :
    QuadraticLocalField.conjugation k d hns ((QuadraticLocalField.algebraEquiv k d hns).symm (Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd).val) =
      -((QuadraticLocalField.algebraEquiv k d hns).symm (Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd).val) := by
  apply (QuadraticLocalField.algebraEquiv k d hns).injective
  rw [QuadraticFieldFrame.model_conjugation, AlgEquiv.apply_symm_apply, map_neg, AlgEquiv.apply_symm_apply]
  ext <;> simp [Weil.AdelicSplitting.Normalization.Construction.deltaUnit]

end RepresentationTheory.Theta.Adelic.IntrinsicOpenCell.IntrinsicScaledForms

namespace RepresentationTheory.Theta.Adelic.IntrinsicOpenCell.Intrinsic

/-! Invertible form matrices and open-cell differences remain invertible
in the actual quadratic field model. -/

open OAI.RepresentationTheory.Weil.UnitarySplitting.FormScaling.Construction
open OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalField OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldForms

variable {k : Type} [Field k] (d : k) (hns : ¬ IsSquare d)
variable {I : Type} [Fintype I] [DecidableEq I]

theorem modelForm_det_ne_zero (A : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) :
    (QuadraticFieldForms.modelForm d hns A.val).det ≠ 0 := by
  let u := Units.map (QuadraticLocalField.algebraEquiv k d hns).symm.toRingHom.mapMatrix.toMonoidHom A
  exact (Matrix.GeneralLinearGroup.det u).ne_zero

theorem modelUnitary_difference (A : Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))
    (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary A) (u : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
    (hu : u.val = g.val.val - 1) :
    (QuadraticFieldForms.modelUnitary d hns A g).val.val - 1 = QuadraticFieldForms.modelForm d hns u.val := by
  rw [hu]
  change (QuadraticLocalField.algebraEquiv k d hns).symm.toRingHom.mapMatrix g.val.val - 1 =
    (QuadraticLocalField.algebraEquiv k d hns).symm.toRingHom.mapMatrix (g.val.val - 1)
  rw [map_sub, map_one]

theorem model_generic_of_difference
    (Q : Matrix I I (QuadraticLocalField.FieldModel k d hns))
    (g : Weil.UnitarySplitting.DualPair.Construction.unitaryGroup (QuadraticLocalField.conjugation k d hns) Q)
    (u : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
    (hu : g.val.val - 1 = QuadraticFieldForms.modelForm d hns u.val) :
    g ∈ Weil.UnitarySplitting.Generic.Construction.unitaryGenericDomain (QuadraticLocalField.conjugation k d hns) Q := by
  change (g.val.val - 1).det ≠ 0
  rw [hu]
  exact modelForm_det_ne_zero d hns u

end RepresentationTheory.Theta.Adelic.IntrinsicOpenCell.Intrinsic

end

end OAI
