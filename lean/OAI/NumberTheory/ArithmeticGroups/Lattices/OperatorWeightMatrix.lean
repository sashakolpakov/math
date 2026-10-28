import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousEndMatrixEquiv
import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.DerivationNilpotence
import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.BlockProjection

/-! # Operator Weight Matrix -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorWeightMatrix.Construction

noncomputable section

/-! Matrix coordinates for weight-raising and weight-preserving
operators in an orthonormal eigenbasis. -/

open scoped Classical _root_.Matrix.Norms.Operator
open _root_.ContinuousLinearMap

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]

theorem continuousEndMatrix_orthonormal_apply {m : ℕ}
    (b : OrthonormalBasis (Fin m) ℝ L) (A : L →L[ℝ] L) (i j : Fin m) :
    ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis A i j = b.repr (A (b j)) i := by
  change LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap i j = _
  rw [LinearMap.toMatrix_apply]
  convert! OrthonormalBasis.coe_toBasis_repr_apply b (A (b j)) i using 1

theorem weightRaising_matrix_iff {m : ℕ}
    (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ) (A : L →L[ℝ] L) :
    A ∈ Positive.DerivationNilpotence.Construction.weightRaisingOperators b w ↔ ∀ i j, w i ≤ w j → ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis A i j = 0 := by
  simp only [continuousEndMatrix_orthonormal_apply]
  rfl

theorem commuting_operator_weight_matrix {m : ℕ}
    (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ)
    (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric) (heig : ∀ i, H (b i) = w i • b i)
    (A : L →L[ℝ] L) (hHA : Commute H A) (i j : Fin m) (hij : w i ≠ w j) :
    ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis A i j = 0 := by
  have he := Positive.DerivationNilpotence.Construction.commutator_eigen_coordinate b H hH w heig A i j
  rw [sub_eq_zero.mpr hHA.eq] at he
  have hz : (w i - w j) * b.repr (A (b j)) i = 0 := by
    simpa only [zero_apply, map_zero, PiLp.zero_apply] using he.symm
  rw [continuousEndMatrix_orthonormal_apply]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hij)

theorem commuting_operator_weightBlockProjection {m : ℕ}
    (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ)
    (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric) (heig : ∀ i, H (b i) = w i • b i)
    (A : L →L[ℝ] L) (hHA : Commute H A) :
    Weight.BlockProjection.Construction.weightBlockProjection w (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis A) = ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis A := by
  ext i j
  rw [Weight.BlockProjection.Construction.weightBlockProjection_apply]
  by_cases hij : w i = w j
  · rw [ite_eq_left hij]
  · rw [ite_eq_right hij, commuting_operator_weight_matrix b w H hH heig A hHA i j hij]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorWeightMatrix.Construction
