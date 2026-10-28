import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorWeightMatrix
import OAI.NumberTheory.ArithmeticGroups.Lattices.FilteredOperatorProjection
import OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalBracketUnitCompactness

/-! # Orthogonal Filtered Projection -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalFilteredProjection.Construction

noncomputable section

/-! An orthogonal operator preserving a weight filtration has no
off-block entries, so its weight-block projection equals itself. -/

open scoped Classical
open _root_.ContinuousLinearMap

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem continuousEndMatrix_adjoint_entry
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (A : L →L[ℝ] L) (i j : Fin m) :
    ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis (adjoint A) i j = ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis A j i := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  rw [OperatorWeightMatrix.Construction.continuousEndMatrix_orthonormal_apply, OperatorWeightMatrix.Construction.continuousEndMatrix_orthonormal_apply,
    b.repr_apply_apply, b.repr_apply_apply, adjoint_inner_right, real_inner_comm]

theorem orthogonal_filtered_weightBlockProjection
    {m : ℕ} (B : L →L[ℝ] L →L[ℝ] L) (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ)
    (g : (L →L[ℝ] L)ˣ) (hg : g ∈ OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup B)
    (hF : g ∈ FilteredOperatorProjection.Construction.weightFilteredOperatorUnits b.toBasis w) :
    Weight.BlockProjection.Construction.weightBlockProjection w (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis g.val) = ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis g.val := by
  have hpos : Matrix.BlockTriangular (α := OrderDual ℝ) (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis g.val) w := hF.1
  have hneg : Matrix.BlockTriangular (α := OrderDual ℝ) (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis (↑g⁻¹)) w := hF.2
  ext i j
  rw [Weight.BlockProjection.Construction.weightBlockProjection_apply]
  by_cases hij : w i = w j
  · rw [ite_eq_left hij]
  · rw [ite_eq_right hij]
    symm
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hpos hlt
    · have he : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis (↑g⁻¹) j i = ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis g.val i j := by
        rw [← OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnit_adjoint_eq_inv B g hg, continuousEndMatrix_adjoint_entry]
      rw [← he]
      exact hneg hgt

theorem orthogonal_filtered_operator_projection_eq
    {m : ℕ} (B : L →L[ℝ] L →L[ℝ] L) (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ)
    (g : (L →L[ℝ] L)ˣ) (hg : g ∈ OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup B)
    (hF : g ∈ FilteredOperatorProjection.Construction.weightFilteredOperatorUnits b.toBasis w) :
    FilteredOperatorProjection.Construction.weightBlockOperatorUnitProjection b.toBasis w ⟨g, hF⟩ = g := by
  apply Units.ext
  apply (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixAlgEquiv b.toBasis).injective
  change ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis (FilteredOperatorProjection.Construction.weightBlockOperatorUnitProjection b.toBasis w ⟨g, hF⟩ : L →L[ℝ] L) =
    ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis g.val
  rw [FilteredOperatorProjection.Construction.weightBlockOperatorUnitProjection_matrix]
  exact orthogonal_filtered_weightBlockProjection B b w g hg hF

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalFilteredProjection.Construction
