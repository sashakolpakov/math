import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorWeightMatrix
import OAI.NumberTheory.ArithmeticGroups.Lattices.FilteredOperatorProjection

/-! # Commuting Filtered Units -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.CommutingFilteredUnits.Construction

noncomputable section

/-! Operators commuting with the symmetric weight operator preserve
the filtration and are fixed by diagonal-block projection. -/

open scoped Classical _root_.Matrix.Norms.Operator
open _root_.ContinuousLinearMap

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem commuting_unit_mem_weightFiltered {m : ℕ}
    (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ)
    (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric) (heig : ∀ i, H (b i) = w i • b i)
    (g : (L →L[ℝ] L)ˣ) (hHg : Commute H (g : L →L[ℝ] L)) :
    g ∈ FilteredOperatorProjection.Construction.weightFilteredOperatorUnits b.toBasis w := by
  have ht (X : L →L[ℝ] L) (hX : Commute H X) :
      Matrix.BlockTriangular (α := OrderDual ℝ) (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis X) w := by
    intro i j hij
    exact OperatorWeightMatrix.Construction.commuting_operator_weight_matrix b w H hH heig X hX i j (ne_of_lt hij)
  constructor
  · change Matrix.BlockTriangular (α := OrderDual ℝ)
      (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis (g : L →L[ℝ] L)) w
    exact ht _ hHg
  · change Matrix.BlockTriangular (α := OrderDual ℝ)
      ((↑((ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis g)⁻¹)) : Matrix (Fin m) (Fin m) ℝ) w
    rw [← map_inv, ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv_val]
    exact ht _ (Commute.units_inv_right hHg)

theorem commuting_unit_weightBlockProjection_eq {m : ℕ}
    (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ)
    (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric) (heig : ∀ i, H (b i) = w i • b i)
    (g : FilteredOperatorProjection.Construction.weightFilteredOperatorUnits b.toBasis w) (hHg : Commute H (g.val : L →L[ℝ] L)) :
    FilteredOperatorProjection.Construction.weightBlockOperatorUnitProjection b.toBasis w g = g.val := by
  apply Units.ext
  apply (ContinuousEndMatrixEquiv.Construction.continuousEndMatrix_bijective b.toBasis).1
  exact (FilteredOperatorProjection.Construction.weightBlockOperatorUnitProjection_matrix b.toBasis w g).trans
    (OperatorWeightMatrix.Construction.commuting_operator_weightBlockProjection b w H hH heig (g.val : L →L[ℝ] L) hHg)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.CommutingFilteredUnits.Construction
