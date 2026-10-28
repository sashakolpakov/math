import OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldForms
import OAI.RepresentationTheory.Weil.AdelicSplitting.SchrodingerPairing

/-! # Quadratic Field Frame -/

namespace OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldFrame

noncomputable section

/-! The native trace-tensor frame gives an UnitarySplitting frame for (H,-K).
This proves the sign and coordinate comparison on the actual tensor space. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.SchrodingerPairing.Construction OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalField OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldForms
open scoped Kronecker

section Algebra
variable {k : Type} [Field k] (d : k) (hns : ¬ IsSquare d)

theorem model_conjugation (x : QuadraticLocalField.FieldModel k d hns) :
    QuadraticLocalField.algebraEquiv k d hns (QuadraticLocalField.conjugation k d hns x) = star (QuadraticLocalField.algebraEquiv k d hns x) := by
  exact (QuadraticLocalField.algebraEquiv k d hns).apply_symm_apply _

theorem modelForm_apply {I J : Type} (A : Matrix I J (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) (i : I) (j : J) :
    QuadraticLocalField.algebraEquiv k d hns (QuadraticFieldForms.modelForm d hns A i j) = A i j :=
  (QuadraticLocalField.algebraEquiv k d hns).apply_symm_apply _

theorem model_sesquilinear {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) (x y : I → QuadraticLocalField.FieldModel k d hns) :
    QuadraticLocalField.algebraEquiv k d hns
      (Weil.UnitarySplitting.DualPair.Construction.sesquilinear (QuadraticLocalField.conjugation k d hns) (QuadraticFieldForms.modelForm d hns A) x y) =
      Weil.AdelicSplitting.TensorSpace.Construction.formValue A (fun i => QuadraticLocalField.algebraEquiv k d hns (x i)) (fun i => QuadraticLocalField.algebraEquiv k d hns (y i)) := by
  simp only [Weil.UnitarySplitting.DualPair.Construction.sesquilinear, Weil.AdelicSplitting.TensorSpace.Construction.formValue, Matrix.mulVec, dotProduct,
    map_sum, map_mul, model_conjugation, modelForm_apply]

variable [CharZero k] {n m : ℕ}

theorem model_tracePairing_neg
    (H : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) (K : Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))
    (x y : Fin n × Fin m → QuadraticLocalField.FieldModel k d hns) :
    Weil.UnitarySplitting.DualPair.Construction.traceTensorPairing (QuadraticLocalField.conjugation k d hns)
      (QuadraticFieldForms.modelForm d hns H) (-(QuadraticFieldForms.modelForm d hns K)) x y =
      -Weil.AdelicSplitting.TensorSpace.Construction.tracePairing d n m H K (fun i => QuadraticLocalField.algebraEquiv k d hns (x i))
        (fun i => QuadraticLocalField.algebraEquiv k d hns (y i)) := by
  have hmat : QuadraticFieldForms.modelForm d hns H ⊗ₖ (-(QuadraticFieldForms.modelForm d hns K)) = -(QuadraticFieldForms.modelForm d hns (H ⊗ₖ K)) := by
    ext i j
    change (QuadraticLocalField.algebraEquiv k d hns).symm (H i.1 j.1) *
      (-(QuadraticLocalField.algebraEquiv k d hns).symm (K i.2 j.2)) =
      -(QuadraticLocalField.algebraEquiv k d hns).symm (H i.1 j.1 * K i.2 j.2)
    rw [map_mul, mul_neg]
  rw [Weil.UnitarySplitting.DualPair.Construction.traceTensorPairing, hmat,
    Weil.UnitarySplitting.TracePairing.Construction.sesquilinear_neg, map_neg, neg_div, QuadraticFieldForms.model_trace,
    model_sesquilinear]
  rfl

end Algebra

variable {k : Type} [NontriviallyNormedField k] [CompleteSpace k] [IsUltrametricDist k] [CharZero k]
variable (d : k) (hns : ¬ IsSquare d) {n m : ℕ}
variable (H : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) (K : Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))

def tensorToNative : ((Fin n × Fin m) → QuadraticLocalField.FieldModel k d hns) ≃ₗ[k] Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d n m :=
  LinearEquiv.piCongrRight (fun _ => (QuadraticLocalField.algebraEquiv k d hns).toLinearEquiv)

def modelFrame (P : Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d n m H K) :
    Weil.UnitarySplitting.Oscillator.Construction.SymplecticFrame (QuadraticLocalField.conjugation k d hns)
      (QuadraticFieldForms.modelForm d hns H) (-(QuadraticFieldForms.modelForm d hns K)) where
  coordinates := (tensorToNative d hns).trans P.coordinates
  preserves x y := by
    rw [model_tracePairing_neg]
    rw [← Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerPairing_eq_standard]
    have h := congrArg (fun z : k => -z) (P.preserves (tensorToNative d hns x) (tensorToNative d hns y))
    change (Matrix.J (Fin (n * m)) k).toBilin'
      (P.coordinates (tensorToNative d hns x)) (P.coordinates (tensorToNative d hns y)) =
      -Weil.AdelicSplitting.TensorSpace.Construction.tracePairing d n m H K (tensorToNative d hns x) (tensorToNative d hns y)
    simpa only [Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing, neg_neg] using h

end

end OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldFrame
