import OAI.NumberTheory.ArithmeticGroups.Lattices.VolumeMatrixOperatorLift
import OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.OperatorSiegelData
import Mathlib.LinearAlgebra.UnitaryGroup

/-! # Orthogonal Operator Matrices -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalOperatorMatrices.Construction

noncomputable section

section

/-! Orthogonal matrices lift to the compact orthogonal factor of the
volume-preserving operator group. -/

open _root_.ContinuousLinearMap
open scoped Classical

def orthogonalMatrixUnit {m : ℕ} (K : Matrix (Fin m) (Fin m) ℝ)
    (hK : K ∈ Matrix.orthogonalGroup (Fin m) ℝ) : (Matrix (Fin m) (Fin m) ℝ)ˣ where
  val := K
  inv := K.transpose
  val_inv := (Matrix.mem_orthogonalGroup_iff (Fin m) ℝ).mp hK
  inv_val := (Matrix.mem_orthogonalGroup_iff' (Fin m) ℝ).mp hK

theorem orthogonal_matrix_abs_det {m : ℕ} (K : Matrix (Fin m) (Fin m) ℝ)
    (hK : K ∈ Matrix.orthogonalGroup (Fin m) ℝ) : |K.det| = 1 := by
  have he := congrArg Matrix.det ((Matrix.mem_orthogonalGroup_iff (Fin m) ℝ).mp hK)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at he
  nlinarith [sq_abs K.det, abs_nonneg K.det]

theorem volume_operator_of_orthogonal_matrix
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (g : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L))
    (hg : (VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom b g).val ∈ Matrix.orthogonalGroup (Fin m) ℝ) :
    g ∈ Ambient.OperatorSiegelData.Construction.ambientSiegelCompact := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  let T := g.val.val
  have he : adjoint T * T = 1 := by
    apply (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixAlgEquiv b.toBasis).injective
    change ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis (adjoint T * T) = ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis 1
    rw [map_mul, map_one]
    have hadj : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis (adjoint T) = (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis T).transpose := by
      ext i j
      exact OrthogonalFilteredProjection.Construction.continuousEndMatrix_adjoint_entry b T i j
    rw [hadj]
    exact (Matrix.mem_orthogonalGroup_iff' (Fin m) ℝ).mp hg
  constructor
  · intro x y
    simp only [zero_apply, map_zero]
  · intro x y
    change inner ℝ (T x) (T y) = inner ℝ x y
    rw [← adjoint_inner_left]
    have hx := DFunLike.congr_fun he x
    change adjoint T (T x) = x at hx
    rw [hx]

end

/-! In orthonormal coordinates, an orthogonal bracket operator has
an orthogonal matrix. -/

open _root_.ContinuousLinearMap

theorem orthogonalBracketUnit_matrix
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (B : L →L[ℝ] L →L[ℝ] L) (g : (L →L[ℝ] L)ˣ)
    (hg : g ∈ OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup B) :
    ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis g.val ∈ Matrix.orthogonalGroup (Fin m) ℝ := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  have ht : (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis g.val).transpose =
      ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis (g⁻¹).val := by
    rw [← OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnit_adjoint_eq_inv B g hg]
    ext i j
    exact (OrthogonalFilteredProjection.Construction.continuousEndMatrix_adjoint_entry b g.val i j).symm
  apply (Matrix.mem_orthogonalGroup_iff (Fin m) ℝ).mpr
  rw [ht, ← map_mul]
  have hi : g.val * (g⁻¹).val = 1 := g.val_inv
  rw [hi, map_one]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalOperatorMatrices.Construction
