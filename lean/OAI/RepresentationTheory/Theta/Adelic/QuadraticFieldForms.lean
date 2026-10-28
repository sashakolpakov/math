import OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalField
import OAI.RepresentationTheory.Weil.UnitarySplitting.QuadraticNorm
import OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace

/-! # Quadratic Field Forms -/

namespace OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldForms

noncomputable section

/-! Transport the native quadratic trace forms and unitary matrices to
the actual nonsplit normed-field model used by UnitarySplitting. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalField

section Algebra
variable {k : Type} [Field k] [CharZero k] (d : k) (hns : ¬ IsSquare d)

theorem model_trace (x : QuadraticLocalField.FieldModel k d hns) :
    Algebra.trace k (QuadraticLocalField.FieldModel k d hns) x = QuadraticAlgebra.trace (QuadraticLocalField.algebraEquiv k d hns x) := by
  have h := Weil.UnitarySplitting.QuadraticNorm.Construction.quadratic_trace_formula (QuadraticLocalField.model_finrank k d hns)
    (QuadraticLocalField.conjugation k d hns) (QuadraticLocalField.conjugation_nontrivial k d hns) x
  have he := congrArg (QuadraticLocalField.algebraEquiv k d hns) h
  rw [AlgEquiv.commutes, map_add] at he
  apply (algebraMap k (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)).injective
  rw [QuadraticAlgebra.algebraMap_trace_eq_add_star]
  exact he

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def modelForm (A : Matrix I J (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) : Matrix I J (QuadraticLocalField.FieldModel k d hns) :=
  A.map (QuadraticLocalField.algebraEquiv k d hns).symm.toRingHom

omit [CharZero k] [Fintype I] [DecidableEq I] in
theorem modelForm_adjoint (A : Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) :
    Weil.UnitarySplitting.DualPair.Construction.adjointMatrix (QuadraticLocalField.conjugation k d hns) (modelForm d hns A) =
      modelForm d hns A.conjTranspose := by
  ext i j
  change (QuadraticLocalField.algebraEquiv k d hns).symm
      (star ((QuadraticLocalField.algebraEquiv k d hns) ((QuadraticLocalField.algebraEquiv k d hns).symm (A j i)))) =
    (QuadraticLocalField.algebraEquiv k d hns).symm (star (A j i))
  rw [AlgEquiv.apply_symm_apply]

def modelUnitary (A : Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) :
    Weil.AdelicSplitting.UnitaryBase.Construction.Unitary A →* Weil.UnitarySplitting.DualPair.Construction.unitaryGroup (QuadraticLocalField.conjugation k d hns) (modelForm d hns A) where
  toFun g := ⟨Units.map (QuadraticLocalField.algebraEquiv k d hns).symm.toRingHom.mapMatrix.toMonoidHom g.val, by
    change Weil.UnitarySplitting.DualPair.Construction.adjointMatrix (QuadraticLocalField.conjugation k d hns) (modelForm d hns g.val.val) *
      modelForm d hns A * modelForm d hns g.val.val = modelForm d hns A
    rw [modelForm_adjoint]
    have h := congrArg (modelForm d hns) g.property
    simpa only [modelForm, Matrix.map_mul] using h⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' g h := by apply Subtype.ext; exact map_mul _ _ _

end Algebra

variable {k : Type} [NontriviallyNormedField k] [CompleteSpace k] [IsUltrametricDist k]
variable (d : k) (hns : ¬ IsSquare d) {I : Type} [Fintype I] [DecidableEq I]

theorem modelUnitary_continuous (A : Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) :
    Continuous (modelUnitary d hns A) := by
  apply Continuous.subtype_mk
  apply Units.continuous_iff.mpr
  constructor <;> apply continuous_pi <;> intro i <;> apply continuous_pi <;> intro j
  · change Continuous (fun g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary A => (QuadraticLocalField.algebraEquiv k d hns).symm (g.val.val i j))
    exact (QuadraticLocalField.coefficientHomeomorph k d hns).symm.continuous.comp
      ((continuous_apply j).comp ((continuous_apply i).comp
        ((Units.continuous_val (M := Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))).comp continuous_subtype_val)))
  · change Continuous (fun g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary A => (QuadraticLocalField.algebraEquiv k d hns).symm ((g.val⁻¹).val i j))
    exact (QuadraticLocalField.coefficientHomeomorph k d hns).symm.continuous.comp
      ((continuous_apply j).comp ((continuous_apply i).comp
        ((Units.continuous_coe_inv (M := Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))).comp continuous_subtype_val)))

end

end OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldForms
