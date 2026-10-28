import OAI.RepresentationTheory.Theta.Adelic.GeneralSplitAction
import OAI.RepresentationTheory.Theta.Adelic.GeneralSplitFrame
import OAI.RepresentationTheory.Weil.Local.Generators

/-! # General Split Tensor Action -/

namespace OAI.RepresentationTheory.Theta.Adelic.GeneralSplitTensorAction

noncomputable section

/-! The complete split unitary pair acts as a Levi subgroup in its actual
stable tensor polarization. -/

open scoped Kronecker

open OAI.RepresentationTheory.Weil.Local.Generators.Construction
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra OAI.RepresentationTheory.Theta.Adelic.SplitUnitary OAI.RepresentationTheory.Theta.Adelic.GeneralSplitAction.Coordinates
open OAI.RepresentationTheory.Theta.Adelic.GeneralSplitFrame OAI.RepresentationTheory.Theta.Adelic.GeneralSplitAction
open _root_.Matrix

variable {k : Type} [Field k] [CharZero k] {d : k}
variable (r : k) (hr : r ^ 2 = d) (hr0 : r ≠ 0) (n m : ℕ)

def reindexUnit : (Matrix (Fin n × Fin m) (Fin n × Fin m) k)ˣ →*
    Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k (n * m) :=
  Units.map (Matrix.reindexRingEquiv k finProdFinEquiv).toMonoidHom

omit [CharZero k] in
theorem reindex_mulVec (A : Matrix (Fin n × Fin m) (Fin n × Fin m) k)
    (x : (Fin n × Fin m) → k) :
    (Matrix.reindex finProdFinEquiv finProdFinEquiv A).mulVec (GeneralSplitFrame.positionReindex n m x) =
      GeneralSplitFrame.positionReindex n m (A.mulVec x) := by
  change A.submatrix finProdFinEquiv.symm finProdFinEquiv.symm *ᵥ
    (x ∘ finProdFinEquiv.symm) = (A *ᵥ x) ∘ finProdFinEquiv.symm
  rw [Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply]

omit [CharZero k] in
theorem reindexUnit_mulVec (A : (Matrix (Fin n × Fin m) (Fin n × Fin m) k)ˣ)
    (x : (Fin n × Fin m) → k) :
    (reindexUnit (k := k) n m A).val.mulVec (GeneralSplitFrame.positionReindex n m x) =
      GeneralSplitFrame.positionReindex n m (A.val.mulVec x) := reindex_mulVec n m A.val x

omit [CharZero k] in
theorem reindexUnit_inverse_transpose_mulVec
    (A : (Matrix (Fin n × Fin m) (Fin n × Fin m) k)ˣ) (x : (Fin n × Fin m) → k) :
    ((reindexUnit (k := k) n m A)⁻¹).val.transpose.mulVec (GeneralSplitFrame.positionReindex n m x) =
      GeneralSplitFrame.positionReindex n m ((A⁻¹).val.transpose.mulVec x) := by
  rw [← map_inv]
  exact reindex_mulVec n m (A⁻¹).val.transpose x

variable (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
variable (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)

def linearPair : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val →* Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k (n * m) :=
  (reindexUnit n m).comp
    ((SplitUnitary.plusUnits r hr hr0).comp
      ((Weil.AdelicSplitting.UnitaryBase.Construction.unitaryMatrix (H.val ⊗ₖ K.val)).comp (Weil.AdelicSplitting.UnitaryBase.Construction.unitaryTensor H.val K.val)))

omit [CharZero k] in
theorem levi_sumElim (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k (n * m)) (q p : Fin (n * m) → k) :
    Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.leviSymplectic A) (Sum.elim q p) =
      Sum.elim (A.val.mulVec q) ((A⁻¹).val.transpose.mulVec p) := by
  funext i
  cases i <;> simp [Weil.Local.FunctionsMetaplectic.Construction.symplecticAction, Weil.Local.Generators.Construction.leviSymplectic, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Matrix.fromBlocks]

theorem phaseCoordinates_intertwines (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val)
    (x : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d n m) :
    GeneralSplitFrame.phaseCoordinates r hr hr0 n m H K (Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear H.val K.val g x) =
      Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.leviSymplectic (linearPair r hr hr0 n m H K g))
        (GeneralSplitFrame.phaseCoordinates r hr hr0 n m H K x) := by
  rw [GeneralSplitFrame.phaseCoordinates_apply, GeneralSplitFrame.phaseCoordinates_apply, levi_sumElim]
  change Sum.elim
      (GeneralSplitFrame.positionReindex n m (GeneralSplitAction.Coordinates.polarizedCoordinates r hr hr0 (Fin n × Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits H K)
        ((Weil.AdelicSplitting.UnitaryBase.Construction.unitaryTensor H.val K.val g).val.val.mulVec x)).1)
      (GeneralSplitFrame.positionReindex n m (GeneralSplitAction.Coordinates.polarizedCoordinates r hr hr0 (Fin n × Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits H K)
        ((Weil.AdelicSplitting.UnitaryBase.Construction.unitaryTensor H.val K.val g).val.val.mulVec x)).2) = _
  rw [GeneralSplitAction.polarizedCoordinates_intertwines r hr hr0 (Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits H K) (Weil.AdelicSplitting.UnitaryBase.Construction.unitaryTensor H.val K.val g) x]
  change Sum.elim _ _ = Sum.elim
    ((reindexUnit n m (SplitUnitary.plusUnits r hr hr0 (Weil.AdelicSplitting.UnitaryBase.Construction.unitaryTensor H.val K.val g).val)).val.mulVec _)
    (((reindexUnit n m (SplitUnitary.plusUnits r hr hr0 (Weil.AdelicSplitting.UnitaryBase.Construction.unitaryTensor H.val K.val g).val))⁻¹).val.transpose.mulVec _)
  rw [reindexUnit_mulVec, reindexUnit_inverse_transpose_mulVec]

theorem splitFrame_action (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val) :
    Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val (GeneralSplitFrame.splitFrame r hr hr0 n m H K hH hK) g =
      Weil.Local.Generators.Construction.leviSymplectic (linearPair r hr hr0 n m H K g) := by
  apply Subtype.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change Matrix.toLin' (LinearMap.toMatrix'
    (Weil.AdelicSplitting.TensorSpace.Construction.coordinateAction H.val K.val (GeneralSplitFrame.splitFrame r hr hr0 n m H K hH hK) g).toLinearMap) x = _
  rw [Matrix.toLin'_toMatrix']
  change GeneralSplitFrame.phaseCoordinates r hr hr0 n m H K
      (Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear H.val K.val g ((GeneralSplitFrame.phaseCoordinates r hr hr0 n m H K).symm x)) = _
  rw [phaseCoordinates_intertwines, LinearEquiv.apply_symm_apply]
  rfl

end

end OAI.RepresentationTheory.Theta.Adelic.GeneralSplitTensorAction
