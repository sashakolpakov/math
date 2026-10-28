import OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentFilteredUnits
import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.ProjectionKernel

/-! # Filtered Operator Kernel -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.FilteredOperatorKernel.Construction

noncomputable section

/-! Identity block projection characterizes the unipotent part of
the filtered operator group. -/

open scoped Classical _root_.Matrix.Norms.Operator

theorem filtered_unit_mem_weightRaising_of_projection_one
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ)
    (g : FilteredOperatorProjection.Construction.weightFilteredOperatorUnits b.toBasis w)
    (hg : FilteredOperatorProjection.Construction.weightBlockOperatorUnitProjection b.toBasis w g = 1) :
    g.val ∈ UnipotentBracketGroup.Construction.weightRaisingUnitGroup b w := by
  have he := FilteredOperatorProjection.Construction.weightBlockOperatorUnitProjection_matrix b.toBasis w g
  rw [hg, Units.val_one, map_one] at he
  have hM : Matrix.BlockTriangular (α := OrderDual ℝ)
      (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis (g.val : L →L[ℝ] L)) w := g.property.1
  apply (OperatorWeightMatrix.Construction.weightRaising_matrix_iff b w ((g.val : L →L[ℝ] L) - 1)).mpr
  intro i j hij
  rw [map_sub, map_one]
  exact Weight.ProjectionKernel.Construction.matrix_filtered_projection_sub_one w _ hM he.symm i j hij

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.FilteredOperatorKernel.Construction
