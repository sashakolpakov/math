import OAI.RepresentationTheory.Weil.UnitarySplitting.FormScaling
import OAI.RepresentationTheory.Weil.UnitarySplitting.TensorFrameCoordinates

/-! # Tensor Model Congruences -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.TensorModelCongruences.Construction

noncomputable section

/-! The two diagonal tensor models and their exact action identities. -/

open _root_.Matrix
open scoped Kronecker

variable {F E : Type} [Field F] [Field E] [Algebra F E] {m n : ℕ}
variable (σ : E ≃ₐ[F] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)

theorem tensorModel_left_congruence (z : E) (u : (Matrix (Fin n) (Fin n) E)ˣ) (a : Fin n → Fˣ)
    (hu : DualPair.Construction.adjointMatrix σ (u : Matrix _ _ E) * K * (u : Matrix _ _ E) = z • TensorUnitary.Construction.multiplicityForm a) :
    Matrix.reindex finProdFinEquiv finProdFinEquiv
      (DualPair.Construction.adjointMatrix σ (DualPair.Construction.tensorUnits (1 : (Matrix (Fin m) (Fin m) E)ˣ) u : Matrix _ _ E) *
        (H ⊗ₖ K) * (DualPair.Construction.tensorUnits (1 : (Matrix (Fin m) (Fin m) E)ˣ) u : Matrix _ _ E)) =
      TensorUnitary.Construction.weightedTensorForm (z • H) a := by
  change Matrix.reindex _ _ (DualPair.Construction.adjointMatrix σ ((1 : Matrix (Fin m) (Fin m) E) ⊗ₖ (u : Matrix _ _ E)) *
    (H ⊗ₖ K) * ((1 : Matrix (Fin m) (Fin m) E) ⊗ₖ (u : Matrix _ _ E))) = _
  rw [DualPair.Construction.adjointMatrix_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    DualPair.Construction.adjointMatrix_one, one_mul, mul_one, hu]
  congr 1
  ext i j
  change H i.1 j.1 * (z * TensorUnitary.Construction.multiplicityForm a i.2 j.2) = (z * H i.1 j.1) * TensorUnitary.Construction.multiplicityForm a i.2 j.2
  ring

theorem tensorModel_left_intertwines (z : E) (u : (Matrix (Fin n) (Fin n) E)ˣ) (a : Fin n → Fˣ)
    (g : DualPair.Construction.unitaryGroup σ H) :
    (DualPair.Construction.tensorUnits (1 : (Matrix (Fin m) (Fin m) E)ˣ) u : Matrix (Fin m × Fin n) (Fin m × Fin n) E) *
        (((TensorUnitary.Construction.weightedTensorUnitary σ (z • H) a (FormScaling.Construction.unitaryScaleForm σ H z g)).val : Matrix _ _ E).submatrix finProdFinEquiv finProdFinEquiv) =
      ((DualPair.Construction.tensorUnitaryAction σ H K (g, 1)).val : Matrix _ _ E) *
        (DualPair.Construction.tensorUnits (1 : (Matrix (Fin m) (Fin m) E)ˣ) u : Matrix _ _ E) := by
  have hr : ((TensorUnitary.Construction.weightedTensorUnitary σ (z • H) a (FormScaling.Construction.unitaryScaleForm σ H z g)).val : Matrix _ _ E).submatrix finProdFinEquiv finProdFinEquiv =
      (g.val : Matrix (Fin m) (Fin m) E) ⊗ₖ (1 : Matrix (Fin n) (Fin n) E) := by
    ext i j
    change ((g.val : Matrix (Fin m) (Fin m) E) ⊗ₖ (1 : Matrix (Fin n) (Fin n) E))
      (finProdFinEquiv.symm (finProdFinEquiv i)) (finProdFinEquiv.symm (finProdFinEquiv j)) = _
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rw [hr]
  change ((1 : Matrix (Fin m) (Fin m) E) ⊗ₖ (u : Matrix (Fin n) (Fin n) E)) * (_ ⊗ₖ 1) =
    (_ ⊗ₖ 1) * (1 ⊗ₖ _)
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [one_mul, mul_one]

def swappedTensorIndex : (Fin m × Fin n) ≃ Fin (n * m) :=
  (Equiv.prodComm (Fin m) (Fin n)).trans finProdFinEquiv

theorem tensorModel_right_congruence (u : (Matrix (Fin m) (Fin m) E)ˣ) (a : Fin m → Fˣ)
    (hu : DualPair.Construction.adjointMatrix σ (u : Matrix _ _ E) * H * (u : Matrix _ _ E) = TensorUnitary.Construction.multiplicityForm a) :
    Matrix.reindex swappedTensorIndex swappedTensorIndex
      (DualPair.Construction.adjointMatrix σ (DualPair.Construction.tensorUnits u (1 : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix _ _ E) *
        (H ⊗ₖ K) * (DualPair.Construction.tensorUnits u (1 : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix _ _ E)) =
      TensorUnitary.Construction.weightedTensorForm K a := by
  change Matrix.reindex _ _ (DualPair.Construction.adjointMatrix σ ((u : Matrix _ _ E) ⊗ₖ (1 : Matrix (Fin n) (Fin n) E)) *
    (H ⊗ₖ K) * ((u : Matrix _ _ E) ⊗ₖ (1 : Matrix (Fin n) (Fin n) E))) = _
  rw [DualPair.Construction.adjointMatrix_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    DualPair.Construction.adjointMatrix_one, one_mul, mul_one, hu]
  ext i j
  change TensorUnitary.Construction.multiplicityForm a (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 *
    K (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 =
    K (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 *
    TensorUnitary.Construction.multiplicityForm a (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2
  exact mul_comm _ _

theorem tensorModel_right_intertwines (u : (Matrix (Fin m) (Fin m) E)ˣ) (a : Fin m → Fˣ)
    (g : DualPair.Construction.unitaryGroup σ K) :
    (DualPair.Construction.tensorUnits u (1 : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin m × Fin n) (Fin m × Fin n) E) *
        (((TensorUnitary.Construction.weightedTensorUnitary σ K a g).val : Matrix _ _ E).submatrix swappedTensorIndex swappedTensorIndex) =
      ((DualPair.Construction.tensorUnitaryAction σ H K (1, g)).val : Matrix _ _ E) *
        (DualPair.Construction.tensorUnits u (1 : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix _ _ E) := by
  have hr : ((TensorUnitary.Construction.weightedTensorUnitary σ K a g).val : Matrix _ _ E).submatrix swappedTensorIndex swappedTensorIndex =
      (1 : Matrix (Fin m) (Fin m) E) ⊗ₖ (g.val : Matrix (Fin n) (Fin n) E) := by
    ext i j
    change ((g.val : Matrix (Fin n) (Fin n) E) ⊗ₖ (1 : Matrix (Fin m) (Fin m) E))
      (finProdFinEquiv.symm (finProdFinEquiv (i.2, i.1)))
      (finProdFinEquiv.symm (finProdFinEquiv (j.2, j.1))) = _
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact mul_comm _ _
  rw [hr]
  change ((u : Matrix (Fin m) (Fin m) E) ⊗ₖ (1 : Matrix (Fin n) (Fin n) E)) * (1 ⊗ₖ _) =
    (1 ⊗ₖ _) * (_ ⊗ₖ 1)
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [one_mul, mul_one]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.TensorModelCongruences.Construction
