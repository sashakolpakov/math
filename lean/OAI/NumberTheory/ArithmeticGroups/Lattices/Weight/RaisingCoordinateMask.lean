import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingSplitFlow
import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousEndMatrixEquiv
import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorWeightMatrix
import Mathlib.LinearAlgebra.Projection

/-! # Raising Coordinate Mask -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingCoordinateMask.Construction

noncomputable section

/-! Coordinate masks split the weight-raising operator space into
complementary subspaces invariant under the regular split flow. -/

open scoped Classical

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

def matrixCoordinateMask {m : ℕ} (r : Fin m → Fin m → Prop) :
    Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ where
  toFun M i j := if r i j then M i j else 0
  map_add' M N := by
    ext i j
    change (if r i j then M i j + N i j else 0) =
      (if r i j then M i j else 0) + (if r i j then N i j else 0)
    split_ifs <;> simp
  map_smul' c M := by
    ext i j
    change (if r i j then c * M i j else 0) = c * (if r i j then M i j else 0)
    split_ifs <;> simp

def operatorCoordinateMask {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (r : Fin m → Fin m → Prop) : (L →L[ℝ] L) →ₗ[ℝ] (L →L[ℝ] L) :=
  (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixAlgEquiv b.toBasis).symm.toLinearMap.comp
    ((matrixCoordinateMask r).comp (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixAlgEquiv b.toBasis).toLinearMap)

theorem operatorCoordinateMask_entry {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (r : Fin m → Fin m → Prop) (X : L →L[ℝ] L) (i j : Fin m) :
    b.repr (operatorCoordinateMask b r X (b j)) i = if r i j then b.repr (X (b j)) i else 0 := by
  rw [← OperatorWeightMatrix.Construction.continuousEndMatrix_orthonormal_apply, ← OperatorWeightMatrix.Construction.continuousEndMatrix_orthonormal_apply]
  change (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixAlgEquiv b.toBasis
    ((ContinuousEndMatrixEquiv.Construction.continuousEndMatrixAlgEquiv b.toBasis).symm (matrixCoordinateMask r
      (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixAlgEquiv b.toBasis X)))) i j = _
  rw [ContinuousAlgEquiv.apply_symm_apply]
  rfl

theorem operatorCoordinateMask_preserves_weightRaising {m : ℕ}
    (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ) (r : Fin m → Fin m → Prop)
    (X : L →L[ℝ] L) (hX : X ∈ Positive.DerivationNilpotence.Construction.weightRaisingOperators b w) :
    operatorCoordinateMask b r X ∈ Positive.DerivationNilpotence.Construction.weightRaisingOperators b w := by
  intro i j hij
  rw [operatorCoordinateMask_entry, hX i j hij]
  split_ifs <;> rfl

def weightRaisingCoordinateMask {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (w : Fin m → ℝ) (r : Fin m → Fin m → Prop) :
    Positive.DerivationNilpotence.Construction.weightRaisingOperators b w →ₗ[ℝ] Positive.DerivationNilpotence.Construction.weightRaisingOperators b w :=
  (operatorCoordinateMask b r).restrict (operatorCoordinateMask_preserves_weightRaising b w r)

theorem weightRaisingCoordinateMask_entry {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (w : Fin m → ℝ) (r : Fin m → Fin m → Prop) (X : Positive.DerivationNilpotence.Construction.weightRaisingOperators b w) (i j : Fin m) :
    b.repr ((weightRaisingCoordinateMask b w r X).val (b j)) i =
      if r i j then b.repr (X.val (b j)) i else 0 := operatorCoordinateMask_entry b r X.val i j

theorem weightRaisingCoordinateMask_idempotent {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (w : Fin m → ℝ) (r : Fin m → Fin m → Prop) : IsIdempotentElem (weightRaisingCoordinateMask b w r) := by
  apply LinearMap.ext
  intro X
  change weightRaisingCoordinateMask b w r (weightRaisingCoordinateMask b w r X) = _
  apply Subtype.ext
  apply (ContinuousEndMatrixEquiv.Construction.continuousEndMatrix_bijective b.toBasis).1
  ext i j
  simp only [OperatorWeightMatrix.Construction.continuousEndMatrix_orthonormal_apply,
    weightRaisingCoordinateMask_entry]
  split_ifs <;> rfl

theorem weightRaisingCoordinateMask_flow_commute {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric)
    (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i)
    (r : Fin m → Fin m → Prop) (t : ℝ) (X : Positive.DerivationNilpotence.Construction.weightRaisingOperators b w) :
    weightRaisingCoordinateMask b w r (RaisingSplitFlow.Construction.weightRaisingSplitFlow b H hH w heig t X) =
      RaisingSplitFlow.Construction.weightRaisingSplitFlow b H hH w heig t (weightRaisingCoordinateMask b w r X) := by
  apply Subtype.ext
  apply (ContinuousEndMatrixEquiv.Construction.continuousEndMatrix_bijective b.toBasis).1
  ext i j
  simp only [OperatorWeightMatrix.Construction.continuousEndMatrix_orthonormal_apply]
  rw [weightRaisingCoordinateMask_entry, RaisingSplitFlow.Construction.weightRaisingSplitFlow_val, RaisingSplitFlow.Construction.weightRaisingSplitFlow_val]
  rw [ConjugationCoordinates.Construction.split_exponential_conjugation_coordinate b H hH w heig,
    ConjugationCoordinates.Construction.split_exponential_conjugation_coordinate b H hH w heig, weightRaisingCoordinateMask_entry]
  split_ifs <;> simp

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingCoordinateMask.Construction
