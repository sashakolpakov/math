import OAI.RepresentationTheory.Theta.Adelic.FieldCharacterTransport
import OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace

/-! # Field Frame Transport -/

namespace OAI.RepresentationTheory.Theta.Adelic.FieldFrameTransport

noncomputable section

/-! Transport the specified native trace-tensor frame through a field
equivalence, with explicit coordinates and pairing preservation. -/

open scoped Kronecker

open OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction OAI.RepresentationTheory.Theta.Adelic.QuadraticNormTransport OAI.RepresentationTheory.Theta.Adelic.FieldCharacterTransport.Unitary

variable {k l : Type} [Field k] [Field l] (e : k ≃+* l) (d : k) {n m : ℕ}

theorem quadraticEquiv_smul (a : k) (x : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) :
    QuadraticNormTransport.quadraticEquiv e d (a • x) = e a • QuadraticNormTransport.quadraticEquiv e d x := by
  ext <;> exact e.map_mul _ _

theorem quadraticEquiv_symm_smul (a : l) (x : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic l (e d)) :
    (QuadraticNormTransport.quadraticEquiv e d).symm (a • x) = e.symm a • (QuadraticNormTransport.quadraticEquiv e d).symm x := by
  apply (QuadraticNormTransport.quadraticEquiv e d).injective
  rw [RingEquiv.apply_symm_apply, quadraticEquiv_smul, e.apply_symm_apply,
    RingEquiv.apply_symm_apply]

def fieldTensorEquiv : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d n m ≃ Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (e d) n m :=
  Equiv.piCongrRight (fun _ => (QuadraticNormTransport.quadraticEquiv e d).toEquiv)

def fieldPhaseEquiv : Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := k) n m ≃ Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := l) n m :=
  Equiv.piCongrRight (fun _ => e.toEquiv)

variable (H : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) (K : Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))

def fieldFrameCoordinates (P : Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d n m H K) :
    Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (e d) n m ≃ₗ[l] Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := l) n m where
  toEquiv := (fieldTensorEquiv e d).symm.trans (P.coordinates.toEquiv.trans (fieldPhaseEquiv e))
  map_add' x y := by
    have ht : (fieldTensorEquiv e d).symm (x + y) =
        (fieldTensorEquiv e d).symm x + (fieldTensorEquiv e d).symm y := by
      funext i
      exact (QuadraticNormTransport.quadraticEquiv e d).symm.map_add _ _
    change (fieldPhaseEquiv e) (P.coordinates ((fieldTensorEquiv e d).symm (x + y))) = _
    rw [ht, map_add]
    funext i
    exact e.map_add _ _
  map_smul' a x := by
    have ht : (fieldTensorEquiv e d).symm (a • x) =
        e.symm a • (fieldTensorEquiv e d).symm x := by
      funext i
      exact quadraticEquiv_symm_smul e d a (x i)
    change (fieldPhaseEquiv e) (P.coordinates ((fieldTensorEquiv e d).symm (a • x))) = _
    rw [ht, map_smul]
    funext i
    change e (e.symm a * P.coordinates ((fieldTensorEquiv e d).symm x) i) =
      a * e (P.coordinates ((fieldTensorEquiv e d).symm x) i)
    rw [map_mul, e.apply_symm_apply]

theorem fieldFrameCoordinates_apply (P : Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d n m H K) (x : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d n m) :
    fieldFrameCoordinates e d H K P (fieldTensorEquiv e d x) = fieldPhaseEquiv e (P.coordinates x) := by
  change fieldPhaseEquiv e (P.coordinates ((fieldTensorEquiv e d).symm (fieldTensorEquiv e d x))) = _
  rw [Equiv.symm_apply_apply]

theorem tracePairing_field (x y : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d n m) :
    Weil.AdelicSplitting.TensorSpace.Construction.tracePairing (e d) n m (FieldCharacterTransport.Unitary.fieldForm e d H) (FieldCharacterTransport.Unitary.fieldForm e d K)
      (fieldTensorEquiv e d x) (fieldTensorEquiv e d y) = e (Weil.AdelicSplitting.TensorSpace.Construction.tracePairing d n m H K x y) := by
  have hstar (z : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) : QuadraticNormTransport.quadraticEquiv e d (star z) = star (QuadraticNormTransport.quadraticEquiv e d z) :=
    Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange_star e.toRingHom d z
  have hform : Weil.AdelicSplitting.TensorSpace.Construction.formValue ((FieldCharacterTransport.Unitary.fieldForm e d H).kronecker (FieldCharacterTransport.Unitary.fieldForm e d K))
      (fieldTensorEquiv e d x) (fieldTensorEquiv e d y) =
        QuadraticNormTransport.quadraticEquiv e d (Weil.AdelicSplitting.TensorSpace.Construction.formValue (H.kronecker K) x y) := by
    simp only [Weil.AdelicSplitting.TensorSpace.Construction.formValue, Matrix.mulVec, dotProduct, map_sum, map_mul, hstar]
    apply Finset.sum_congr rfl
    intro i _
    change star (QuadraticNormTransport.quadraticEquiv e d (x i)) *
      (∑ j, (QuadraticNormTransport.quadraticEquiv e d (H i.1 j.1) * QuadraticNormTransport.quadraticEquiv e d (K i.2 j.2)) * QuadraticNormTransport.quadraticEquiv e d (y j)) =
      star (QuadraticNormTransport.quadraticEquiv e d (x i)) *
      (∑ j, QuadraticNormTransport.quadraticEquiv e d (H i.1 j.1 * K i.2 j.2) * QuadraticNormTransport.quadraticEquiv e d (y j))
    simp only [map_mul]
  have htrace (z : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) : QuadraticAlgebra.trace (QuadraticNormTransport.quadraticEquiv e d z) =
      e (QuadraticAlgebra.trace z) := by
    simp [QuadraticAlgebra.trace_def, QuadraticNormTransport.quadraticEquiv, Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange, map_mul, map_ofNat]
  have h := congrArg (fun z : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic l (e d) => QuadraticAlgebra.trace z / 2) hform
  exact h.trans (by
    change QuadraticAlgebra.trace (QuadraticNormTransport.quadraticEquiv e d (Weil.AdelicSplitting.TensorSpace.Construction.formValue (H.kronecker K) x y)) / 2 =
      e (QuadraticAlgebra.trace (Weil.AdelicSplitting.TensorSpace.Construction.formValue (H.kronecker K) x y) / 2)
    rw [htrace, map_div₀, map_ofNat])

theorem coordinatePairing_field (x y : Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := k) n m) :
    Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing n m (fieldPhaseEquiv e x) (fieldPhaseEquiv e y) = e (Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing n m x y) := by
  have hJ : ((Matrix.J (Fin (n * m)) k).map e) = Matrix.J (Fin (n * m)) l := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.J, Matrix.fromBlocks, Matrix.one_apply]
  have h : e ((Matrix.J (Fin (n * m)) k).toBilin' x y) =
      ((Matrix.J (Fin (n * m)) k).map e).toBilin'
        (fieldPhaseEquiv e x) (fieldPhaseEquiv e y) := by
    simp only [Matrix.toBilin'_apply, map_sum, map_mul]
    rfl
  rw [hJ] at h
  exact (congrArg Neg.neg h.symm).trans (e.map_neg ((Matrix.J (Fin (n * m)) k).toBilin' x y)).symm

def fieldFrame (P : Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d n m H K) :
    Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame (e d) n m (FieldCharacterTransport.Unitary.fieldForm e d H) (FieldCharacterTransport.Unitary.fieldForm e d K) where
  coordinates := fieldFrameCoordinates e d H K P
  preserves x y := by
    obtain ⟨x, rfl⟩ := (fieldTensorEquiv e d).surjective x
    obtain ⟨y, rfl⟩ := (fieldTensorEquiv e d).surjective y
    rw [fieldFrameCoordinates_apply, fieldFrameCoordinates_apply, coordinatePairing_field,
      P.preserves, tracePairing_field]

end

end OAI.RepresentationTheory.Theta.Adelic.FieldFrameTransport
