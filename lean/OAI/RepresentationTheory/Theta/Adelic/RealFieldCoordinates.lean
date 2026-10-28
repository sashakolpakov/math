import OAI.RepresentationTheory.Theta.Adelic.RealQuadraticField
import OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldAction

/-! # Real Field Coordinates -/

namespace OAI.RepresentationTheory.Theta.Adelic.RealFieldCoordinates

noncomputable section

/-! Native coefficient topology, symplectic frames, and tensor actions
for the real quadratic field model. -/

open OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalField OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldForms OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldFrame
open OAI.RepresentationTheory.Theta.Adelic.QuadraticFieldAction OAI.RepresentationTheory.Theta.Adelic.CircleCoordinates

variable (d : ℝ) (hns : ¬ IsSquare d)

def realCoordinates : QuadraticLocalField.FieldModel ℝ d hns ≃L[ℝ] (Fin 2 → ℝ) :=
  (QuadraticLocalField.modelBasis ℝ d hns).equivFun.toContinuousLinearEquiv

theorem realCoordinates_apply (x : QuadraticLocalField.FieldModel ℝ d hns) :
    realCoordinates d hns x = ![(QuadraticLocalField.algebraEquiv ℝ d hns x).re, (QuadraticLocalField.algebraEquiv ℝ d hns x).im] := rfl

def realHomeomorph : QuadraticLocalField.FieldModel ℝ d hns ≃ₜ Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d where
  toEquiv := (QuadraticLocalField.algebraEquiv ℝ d hns).toEquiv
  continuous_toFun := by
    rw [Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_iff]
    exact ⟨(continuous_apply 0).comp (realCoordinates d hns).continuous,
      (continuous_apply 1).comp (realCoordinates d hns).continuous⟩
  continuous_invFun := by
    have hc : Continuous (fun x : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d => ![x.re, x.im]) := by
      apply continuous_pi
      intro i
      fin_cases i
      · exact Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_re d
      · exact Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_im d
    have he : (fun x : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d => (QuadraticLocalField.algebraEquiv ℝ d hns).symm x) =
        (fun x => (realCoordinates d hns).symm ![x.re, x.im]) := by
      funext x
      apply (realCoordinates d hns).injective
      rw [ContinuousLinearEquiv.apply_symm_apply, realCoordinates_apply, AlgEquiv.apply_symm_apply]
    change Continuous (fun x : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d => (QuadraticLocalField.algebraEquiv ℝ d hns).symm x)
    rw [he]
    exact (realCoordinates d hns).symm.continuous.comp hc

variable {n m : ℕ}
variable (H : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d)) (K : Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d))

def realTensorToNative : ((Fin n × Fin m) → QuadraticLocalField.FieldModel ℝ d hns) ≃ₗ[ℝ] Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d n m :=
  LinearEquiv.piCongrRight (fun _ => (QuadraticLocalField.algebraEquiv ℝ d hns).toLinearEquiv)

def realModelFrame (P : Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d n m H K) :
    Weil.UnitarySplitting.Oscillator.Construction.SymplecticFrame (QuadraticLocalField.conjugation ℝ d hns)
      (QuadraticFieldForms.modelForm d hns H) (-(QuadraticFieldForms.modelForm d hns K)) where
  coordinates := (realTensorToNative d hns).trans P.coordinates
  preserves x y := by
    rw [QuadraticFieldFrame.model_tracePairing_neg]
    rw [← Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerPairing_eq_standard]
    have h := congrArg (fun z : ℝ => -z) (P.preserves (realTensorToNative d hns x) (realTensorToNative d hns y))
    change (Matrix.J (Fin (n * m)) ℝ).toBilin'
      (P.coordinates (realTensorToNative d hns x)) (P.coordinates (realTensorToNative d hns y)) =
      -Weil.AdelicSplitting.TensorSpace.Construction.tracePairing d n m H K (realTensorToNative d hns x) (realTensorToNative d hns y)
    simpa only [Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing, neg_neg] using h

section MatrixTopology
variable {I : Type} [Fintype I] [DecidableEq I]

theorem realModelUnitary_continuous (A : Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d)) :
    Continuous (QuadraticFieldForms.modelUnitary d hns A) := by
  apply Continuous.subtype_mk
  apply Units.continuous_iff.mpr
  constructor <;> apply continuous_pi <;> intro i <;> apply continuous_pi <;> intro j
  · change Continuous (fun g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary A => (QuadraticLocalField.algebraEquiv ℝ d hns).symm (g.val.val i j))
    exact (realHomeomorph d hns).symm.continuous.comp
      ((continuous_apply j).comp ((continuous_apply i).comp
        ((Units.continuous_val (M := Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d))).comp continuous_subtype_val)))
  · change Continuous (fun g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary A => (QuadraticLocalField.algebraEquiv ℝ d hns).symm ((g.val⁻¹).val i j))
    exact (realHomeomorph d hns).symm.continuous.comp
      ((continuous_apply j).comp ((continuous_apply i).comp
        ((Units.continuous_coe_inv (M := Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d))).comp continuous_subtype_val)))

end MatrixTopology

def realModelPairContinuous : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K →ₜ*
    Weil.UnitarySplitting.DualPair.Construction.unitaryGroup (QuadraticLocalField.conjugation ℝ d hns) (QuadraticFieldForms.modelForm d hns H) ×
      Weil.UnitarySplitting.DualPair.Construction.unitaryGroup (QuadraticLocalField.conjugation ℝ d hns) (-(QuadraticFieldForms.modelForm d hns K)) :=
  { QuadraticFieldAction.modelPair d hns H K with
    continuous_toFun := ((realModelUnitary_continuous d hns H).comp continuous_fst).prodMk
      (((QuadraticFieldAction.negateUnitary_continuous (QuadraticLocalField.conjugation ℝ d hns) (QuadraticFieldForms.modelForm d hns K)).comp
        (realModelUnitary_continuous d hns K)).comp continuous_snd) }

theorem realModel_dualPair_coordinates (P : Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d n m H K) (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K) :
    CircleCoordinates.coordinateSymplectic (QuadraticLocalField.conjugation ℝ d hns) (QuadraticFieldForms.modelForm d hns H) (-(QuadraticFieldForms.modelForm d hns K))
      (realModelFrame d hns H K P)
      (Weil.UnitarySplitting.DualPair.Construction.dualPairAction (QuadraticLocalField.conjugation ℝ d hns)
        (QuadraticFieldForms.modelForm d hns H) (-(QuadraticFieldForms.modelForm d hns K)) (QuadraticFieldAction.modelPair d hns H K g)) =
      Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H K P g := by
  let c := realModelFrame d hns H K P
  have hpre (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (n * m)) :
      realTensorToNative d hns (c.coordinates.symm v) = P.coordinates.symm v := by
    apply P.coordinates.injective
    change c.coordinates (c.coordinates.symm v) = P.coordinates (P.coordinates.symm v)
    rw [c.coordinates.apply_symm_apply, P.coordinates.apply_symm_apply]
  have hnative (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (n * m)) : Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H K P g) v =
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
  change P.coordinates (realTensorToNative d hns
      ((Weil.UnitarySplitting.DualPair.Construction.dualPairAction (QuadraticLocalField.conjugation ℝ d hns)
        (QuadraticFieldForms.modelForm d hns H) (-(QuadraticFieldForms.modelForm d hns K)) (QuadraticFieldAction.modelPair d hns H K g)).val (c.coordinates.symm v))) = _
  have ht := QuadraticFieldAction.model_tensor_action d hns H K g (c.coordinates.symm v)
  change realTensorToNative d hns _ = Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear H K g (realTensorToNative d hns (c.coordinates.symm v)) at ht
  exact congrArg P.coordinates (ht.trans (congrArg (Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear H K g) (hpre v)))

end

end OAI.RepresentationTheory.Theta.Adelic.RealFieldCoordinates
