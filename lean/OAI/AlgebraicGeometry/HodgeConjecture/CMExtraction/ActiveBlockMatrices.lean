import OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimeBareLift
import OAI.RepresentationTheory.Weil.Local.SpecialLinearCommutators
import OAI.RepresentationTheory.Theta.Geometric.SphericalGU

/-! # Active Block Matrices -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveBlockMatrices.Local

noncomputable section

/-! Embed the active SL3 into the actual full local position coordinates,
with identity on every other place and determinant exactly one. -/

open OAI.RepresentationTheory.Weil.Local.SpecialLinearCommutators.Construction
open scoped Classical _root_.Matrix

variable {k : Type} [Field k] {Place : Type} [Fintype Place] [DecidableEq Place]
  {n : ℕ} (e : (Place × Fin 3) ≃ Fin n) (μ : Place)

def activeBlockMatrix (g : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin n) (Fin n) k :=
  Matrix.reindex ((Equiv.prodComm (Fin 3) Place).trans e)
    ((Equiv.prodComm (Fin 3) Place).trans e)
    (Matrix.blockDiagonal (fun τ : Place => if τ = μ then g.val else 1))

theorem activeBlockMatrix_one : activeBlockMatrix e μ (1 : Matrix.SpecialLinearGroup (Fin 3) k) = 1 := by
  unfold activeBlockMatrix
  simp only [Matrix.SpecialLinearGroup.coe_one, ite_self]
  let R := Matrix.reindexRingEquiv k ((Equiv.prodComm (Fin 3) Place).trans e)
  change R (Matrix.blockDiagonal (1 : Place → Matrix (Fin 3) (Fin 3) k)) = 1
  rw [Matrix.blockDiagonal_one, map_one]

theorem activeBlockMatrix_mul (g h : Matrix.SpecialLinearGroup (Fin 3) k) :
    activeBlockMatrix e μ (g * h) = activeBlockMatrix e μ g * activeBlockMatrix e μ h := by
  let R := Matrix.reindexRingEquiv k ((Equiv.prodComm (Fin 3) Place).trans e)
  change R (Matrix.blockDiagonal (fun τ : Place => if τ = μ then (g * h).val else 1)) =
    R (Matrix.blockDiagonal (fun τ : Place => if τ = μ then g.val else 1)) *
      R (Matrix.blockDiagonal (fun τ : Place => if τ = μ then h.val else 1))
  rw [← map_mul]
  apply congrArg R
  rw [← Matrix.blockDiagonal_mul]
  congr 1
  funext τ
  by_cases ht : τ = μ <;> simp [ht]

theorem activeBlockMatrix_det (g : Matrix.SpecialLinearGroup (Fin 3) k) :
    (activeBlockMatrix e μ g).det = 1 := by
  rw [activeBlockMatrix, Matrix.det_reindex_self, Matrix.det_blockDiagonal]
  apply Finset.prod_eq_one
  intro τ _
  split_ifs
  · exact g.property
  · exact Matrix.det_one

def activeBlockGL : Matrix.SpecialLinearGroup (Fin 3) k →* RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k n where
  toFun g :=
    { val := activeBlockMatrix e μ g
      inv := activeBlockMatrix e μ g⁻¹
      val_inv := by rw [← activeBlockMatrix_mul, mul_inv_cancel, activeBlockMatrix_one]
      inv_val := by rw [← activeBlockMatrix_mul, inv_mul_cancel, activeBlockMatrix_one] }
  map_one' := Units.ext (activeBlockMatrix_one e μ)
  map_mul' g h := Units.ext (activeBlockMatrix_mul e μ g h)

theorem activeBlockGL_det (g : Matrix.SpecialLinearGroup (Fin 3) k) :
    (activeBlockGL e μ g).val.det = 1 := activeBlockMatrix_det e μ g

omit [Fintype Place] in
theorem activeBlockMatrix_entry (g : Matrix.SpecialLinearGroup (Fin 3) k)
    (τ υ : Place) (i j : Fin 3) :
    activeBlockMatrix e μ g (e (τ, i)) (e (υ, j)) =
      if τ = υ then (if τ = μ then g.val i j else (1 : Matrix (Fin 3) (Fin 3) k) i j) else 0 := by
  simp only [activeBlockMatrix, Matrix.reindex_apply, Matrix.submatrix_apply]
  change (if (e.symm (e (τ, i))).1 = (e.symm (e (υ, j))).1 then
    (if (e.symm (e (τ, i))).1 = μ then g.val else 1)
      (e.symm (e (τ, i))).2 (e.symm (e (υ, j))).2 else 0) = _
  simp only [Equiv.symm_apply_apply]
  split_ifs <;> rfl

theorem activeBlockMatrix_mulVec (g : Matrix.SpecialLinearGroup (Fin 3) k)
    (x : Fin n → k) (τ : Place) (i : Fin 3) :
    (activeBlockMatrix e μ g *ᵥ x) (e (τ, i)) =
      if τ = μ then (g.val *ᵥ (fun j => x (e (μ, j)))) i else x (e (τ, i)) := by
  change (∑ j : Fin n, activeBlockMatrix e μ g (e (τ, i)) j * x j) = _
  rw [← e.sum_comp]
  simp only [Fintype.sum_prod_type, activeBlockMatrix_entry]
  by_cases ht : τ = μ
  · subst τ
    simp [Matrix.mulVec, dotProduct]
  · simp [ht, Matrix.one_apply]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveBlockMatrices.Local
