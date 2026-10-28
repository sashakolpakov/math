import OAI.RepresentationTheory.Theta.Adelic.FieldFrameTransport
import OAI.RepresentationTheory.Weil.Local.FieldFourier

/-! # Field Tensor Transport -/

namespace OAI.RepresentationTheory.Theta.Adelic.FieldTensorTransport

noncomputable section

/-! The field-transformed tensor action is exactly the native matrix
action in the transported frame. -/

open scoped Kronecker

open OAI.RepresentationTheory.Weil.Local.FieldFourier.Construction
open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormTransport OAI.RepresentationTheory.Theta.Adelic.FieldCharacterTransport.Unitary OAI.RepresentationTheory.Theta.Adelic.FieldFrameTransport

section Algebra
variable {k l : Type} [Field k] [Field l] (e : k ≃+* l) (d : k) {n m : ℕ}
variable (H : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) (K : Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))

def fieldPairMap : (Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K) →* (Weil.AdelicSplitting.UnitaryBase.Construction.Unitary (FieldCharacterTransport.Unitary.fieldForm e d H) × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary (FieldCharacterTransport.Unitary.fieldForm e d K)) :=
  (FieldCharacterTransport.Unitary.fieldUnitaryMap e d H).prodMap (FieldCharacterTransport.Unitary.fieldUnitaryMap e d K)

theorem tensorLinear_field (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K) (x : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d n m) :
    Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear (FieldCharacterTransport.Unitary.fieldForm e d H) (FieldCharacterTransport.Unitary.fieldForm e d K) (fieldPairMap e d H K g)
      (FieldFrameTransport.fieldTensorEquiv e d x) = FieldFrameTransport.fieldTensorEquiv e d (Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear H K g x) := by
  funext i
  change (((g.1.val.val.map (QuadraticNormTransport.quadraticEquiv e d).toRingHom).kronecker
    (g.2.val.val.map (QuadraticNormTransport.quadraticEquiv e d).toRingHom)).mulVec
    (fun j => QuadraticNormTransport.quadraticEquiv e d (x j))) i =
      QuadraticNormTransport.quadraticEquiv e d ((g.1.val.val.kronecker g.2.val.val).mulVec x i)
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem fieldFrame_symm (P : Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d n m H K) (x : Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := k) n m) :
    (FieldFrameTransport.fieldFrame e d H K P).coordinates.symm (FieldFrameTransport.fieldPhaseEquiv e x) =
      FieldFrameTransport.fieldTensorEquiv e d (P.coordinates.symm x) := by
  apply (FieldFrameTransport.fieldFrame e d H K P).coordinates.injective
  rw [LinearEquiv.apply_symm_apply]
  change _ = FieldFrameTransport.fieldFrameCoordinates e d H K P (FieldFrameTransport.fieldTensorEquiv e d (P.coordinates.symm x))
  rw [FieldFrameTransport.fieldFrameCoordinates_apply, P.coordinates.apply_symm_apply]

theorem coordinateAction_field (P : Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d n m H K)
    (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K) (x : Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := k) n m) :
    Weil.AdelicSplitting.TensorSpace.Construction.coordinateAction (FieldCharacterTransport.Unitary.fieldForm e d H) (FieldCharacterTransport.Unitary.fieldForm e d K) (FieldFrameTransport.fieldFrame e d H K P)
      (fieldPairMap e d H K g) (FieldFrameTransport.fieldPhaseEquiv e x) =
        FieldFrameTransport.fieldPhaseEquiv e (Weil.AdelicSplitting.TensorSpace.Construction.coordinateAction H K P g x) := by
  change (FieldFrameTransport.fieldFrame e d H K P).coordinates
    (Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear (FieldCharacterTransport.Unitary.fieldForm e d H) (FieldCharacterTransport.Unitary.fieldForm e d K) (fieldPairMap e d H K g)
      ((FieldFrameTransport.fieldFrame e d H K P).coordinates.symm (FieldFrameTransport.fieldPhaseEquiv e x))) = _
  rw [fieldFrame_symm, tensorLinear_field]
  exact FieldFrameTransport.fieldFrameCoordinates_apply e d H K P _

theorem dualPairSymplectic_field (P : Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d n m H K) (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K) :
    Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic (FieldCharacterTransport.Unitary.fieldForm e d H) (FieldCharacterTransport.Unitary.fieldForm e d K) (FieldFrameTransport.fieldFrame e d H K P)
      (fieldPairMap e d H K g) = Weil.Local.FieldFourier.Construction.fieldSymplecticMap e (n * m) (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H K P g) := by
  classical
  apply Subtype.ext
  ext i j
  change Weil.AdelicSplitting.TensorSpace.Construction.coordinateAction _ _ (FieldFrameTransport.fieldFrame e d H K P) _ (Pi.single j 1) i =
    e (Weil.AdelicSplitting.TensorSpace.Construction.coordinateAction H K P g (Pi.single j 1) i)
  have heq : (Pi.single j 1 : Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := l) n m) =
      FieldFrameTransport.fieldPhaseEquiv e (Pi.single j 1 : Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := k) n m) := by
    funext a
    change (Pi.single j (1 : l) : Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := l) n m) a =
      e ((Pi.single j (1 : k) : Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := k) n m) a)
    by_cases ha : a = j
    · subst a
      simp only [Pi.single_eq_same, map_one]
    · simp only [Pi.single_eq_of_ne ha, map_zero]
  rw [heq]
  exact congrFun (coordinateAction_field e d H K P g (Pi.single j 1)) i

end Algebra

variable {k l : Type} [NormedField k] [NormedField l]
variable (e : k ≃+* l) (he : Continuous e) (d : k) {n m : ℕ}
variable (H : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) (K : Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))

def fieldPairContinuous : (Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K) →ₜ* (Weil.AdelicSplitting.UnitaryBase.Construction.Unitary (FieldCharacterTransport.Unitary.fieldForm e d H) × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary (FieldCharacterTransport.Unitary.fieldForm e d K)) :=
  { fieldPairMap e d H K with
    continuous_toFun := ((FieldCharacterTransport.Unitary.fieldUnitaryMap_continuous e he d H).comp continuous_fst).prodMk
      ((FieldCharacterTransport.Unitary.fieldUnitaryMap_continuous e he d K).comp continuous_snd) }

end

end OAI.RepresentationTheory.Theta.Adelic.FieldTensorTransport
