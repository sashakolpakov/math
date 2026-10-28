import OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldFrame
import OAI.RepresentationTheory.Theta.Adelic.CircleCoordinates

/-! # Quadratic Field Action -/

namespace OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldAction

noncomputable section

/-! The transported UnitarySplitting tensor action is exactly the native local
dual-pair matrix action in the specified frame. -/

open OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalField OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldForms OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldFrame OAI.RepresentationTheory.Theta.Adelic.CircleCoordinates

section Negation
variable {k E I : Type} [Field k] [Field E] [Algebra k E] [Fintype I] [DecidableEq I]

def negateUnitary (σ : E ≃ₐ[k] E) (Q : Matrix I I E) :
    Weil.UnitarySplitting.DualPair.Construction.unitaryGroup σ Q →*
      Weil.UnitarySplitting.DualPair.Construction.unitaryGroup σ (-Q) where
  toFun g := ⟨g.val, by
    change Weil.UnitarySplitting.DualPair.Construction.adjointMatrix σ g.val.val * (-Q) * g.val.val = -Q
    rw [Matrix.mul_neg, Matrix.neg_mul, g.property]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem negateUnitary_continuous [TopologicalSpace E] (σ : E ≃ₐ[k] E) (Q : Matrix I I E) :
    Continuous (negateUnitary σ Q) := continuous_subtype_val.subtype_mk _

end Negation

section Algebra
variable {k : Type} [Field k] (d : k) (hns : ¬ IsSquare d) {n m : ℕ}
variable (H : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) (K : Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))

def modelPair : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K →*
    Weil.UnitarySplitting.DualPair.Construction.unitaryGroup (QuadraticLocalField.conjugation k d hns) (QuadraticFieldForms.modelForm d hns H) ×
      Weil.UnitarySplitting.DualPair.Construction.unitaryGroup (QuadraticLocalField.conjugation k d hns) (-(QuadraticFieldForms.modelForm d hns K)) :=
  (QuadraticFieldForms.modelUnitary d hns H).prodMap
    ((negateUnitary (QuadraticLocalField.conjugation k d hns) (QuadraticFieldForms.modelForm d hns K)).comp (QuadraticFieldForms.modelUnitary d hns K))

theorem model_tensor_action (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K)
    (x : Fin n × Fin m → QuadraticLocalField.FieldModel k d hns) :
    (fun i => QuadraticLocalField.algebraEquiv k d hns
      ((Weil.UnitarySplitting.DualPair.Construction.dualPairAction (QuadraticLocalField.conjugation k d hns)
        (QuadraticFieldForms.modelForm d hns H) (-(QuadraticFieldForms.modelForm d hns K)) (modelPair d hns H K g)).val x i)) =
      Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear H K g (fun i => QuadraticLocalField.algebraEquiv k d hns (x i)) := by
  funext i
  change (QuadraticLocalField.algebraEquiv k d hns)
    (∑ j : Fin n × Fin m, ((QuadraticLocalField.algebraEquiv k d hns).symm (g.1.val.val i.1 j.1) *
      (QuadraticLocalField.algebraEquiv k d hns).symm (g.2.val.val i.2 j.2)) * x j) =
    ∑ j : Fin n × Fin m, (g.1.val.val i.1 j.1 * g.2.val.val i.2 j.2) * QuadraticLocalField.algebraEquiv k d hns (x j)
  simp only [map_sum, map_mul, AlgEquiv.apply_symm_apply]

end Algebra

variable {k : Type} [NontriviallyNormedField k] [CompleteSpace k] [IsUltrametricDist k] [CharZero k]
variable (d : k) (hns : ¬ IsSquare d) {n m : ℕ}
variable (H : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) (K : Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))

omit [CharZero k] in
def modelPairContinuous : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K →ₜ*
    Weil.UnitarySplitting.DualPair.Construction.unitaryGroup (QuadraticLocalField.conjugation k d hns) (QuadraticFieldForms.modelForm d hns H) ×
      Weil.UnitarySplitting.DualPair.Construction.unitaryGroup (QuadraticLocalField.conjugation k d hns) (-(QuadraticFieldForms.modelForm d hns K)) :=
  { modelPair d hns H K with
    continuous_toFun := ((QuadraticFieldForms.modelUnitary_continuous d hns H).comp continuous_fst).prodMk
      (((negateUnitary_continuous (QuadraticLocalField.conjugation k d hns) (QuadraticFieldForms.modelForm d hns K)).comp
        (QuadraticFieldForms.modelUnitary_continuous d hns K)).comp continuous_snd) }

theorem model_dualPair_coordinates (P : Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d n m H K) (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K) :
    CircleCoordinates.coordinateSymplectic (QuadraticLocalField.conjugation k d hns) (QuadraticFieldForms.modelForm d hns H) (-(QuadraticFieldForms.modelForm d hns K))
      (QuadraticFieldFrame.modelFrame d hns H K P)
      (Weil.UnitarySplitting.DualPair.Construction.dualPairAction (QuadraticLocalField.conjugation k d hns)
        (QuadraticFieldForms.modelForm d hns H) (-(QuadraticFieldForms.modelForm d hns K)) (modelPair d hns H K g)) =
      Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H K P g := by
  let c := QuadraticFieldFrame.modelFrame d hns H K P
  have hpre (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k (n * m)) :
      QuadraticFieldFrame.tensorToNative d hns (c.coordinates.symm v) = P.coordinates.symm v := by
    apply P.coordinates.injective
    change c.coordinates (c.coordinates.symm v) = P.coordinates (P.coordinates.symm v)
    rw [c.coordinates.apply_symm_apply, P.coordinates.apply_symm_apply]
  have hnative (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k (n * m)) : Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H K P g) v =
      P.coordinates (Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear H K g (P.coordinates.symm v)) := by
    change Matrix.toLin' (LinearMap.toMatrix' (Weil.AdelicSplitting.TensorSpace.Construction.coordinateAction H K P g).toLinearMap) v = _
    rw [Matrix.toLin'_toMatrix']
    rfl
  apply Subtype.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  change Weil.Local.FunctionsMetaplectic.Construction.symplecticAction _ v = Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H K P g) v
  rw [CircleCoordinates.coordinateSymplectic_apply, hnative]
  change P.coordinates (QuadraticFieldFrame.tensorToNative d hns
      ((Weil.UnitarySplitting.DualPair.Construction.dualPairAction (QuadraticLocalField.conjugation k d hns)
        (QuadraticFieldForms.modelForm d hns H) (-(QuadraticFieldForms.modelForm d hns K)) (modelPair d hns H K g)).val (c.coordinates.symm v))) = _
  have ht := model_tensor_action d hns H K g (c.coordinates.symm v)
  change QuadraticFieldFrame.tensorToNative d hns _ = Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear H K g (QuadraticFieldFrame.tensorToNative d hns (c.coordinates.symm v)) at ht
  exact congrArg P.coordinates (ht.trans (congrArg (Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear H K g) (hpre v)))

end

end OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldAction
