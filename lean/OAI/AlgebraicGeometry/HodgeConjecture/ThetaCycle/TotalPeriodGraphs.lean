import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ComplexTransition
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BlockPeriod

/-! # Total Period Graphs -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TotalPeriodGraphs.CM

noncomputable section

/-! ThetaCycle: the total block period is the actual direct sum of the line graphs. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}

def totalGraphInAmbient (C : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (PeriodTotal.CM.TotalPositions K places)) :
    (PeriodTotal.CM.TotalPositions K places → ℂ) →ₗ[ℂ] ComplexTransition.CM.TotalAmbient K :=
  (ComplexTransition.CM.totalComplexCoordinates K C).symm.toLinearMap.comp <|
    (LinearEquiv.sumArrowLequivProdArrow (PeriodTotal.CM.TotalPositions K places)
      (PeriodTotal.CM.TotalPositions K places) ℂ ℂ).symm.toLinearMap.comp <|
      (Matrix.toLin' Z.matrix).prod LinearMap.id

theorem total_graph_coordinates (C : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (PeriodTotal.CM.TotalPositions K places)) (x : PeriodTotal.CM.TotalPositions K places → ℂ) :
    ComplexTransition.CM.totalComplexCoordinates K C (totalGraphInAmbient K C Z x) =
      Sum.elim (Z.matrix *ᵥ x) x := by
  change ComplexTransition.CM.totalComplexCoordinates K C ((ComplexTransition.CM.totalComplexCoordinates K C).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem total_block_graph
    (C : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (Z₀ Z₁ : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (HeckeCycles.GeometricSource.CM.Positions K places)) (x : PeriodTotal.CM.TotalPositions K places → ℂ) :
    totalGraphInAmbient K C (BlockPeriod.CM.blockPeriod Z₀ Z₁) x =
      ![HeckeCycles.GeometricSource.CM.graphInAmbient K (C 0) Z₀ (fun j => x (Sum.inl j)),
        HeckeCycles.GeometricSource.CM.graphInAmbient K (C 1) Z₁ (fun j => x (Sum.inr j))] := by
  apply (ComplexTransition.CM.totalComplexCoordinates K C).injective
  rw [total_graph_coordinates]
  have hg (i : Fin 2) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (HeckeCycles.GeometricSource.CM.Positions K places)) (y : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
      (C i).complex (HeckeCycles.GeometricSource.CM.graphInAmbient K (C i) Z y) = (Z.matrix *ᵥ y, y) := by
    change (C i).complex ((C i).complex.symm _) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  funext i
  rcases i with i | i <;> rcases i with i | i
  · change ((BlockPeriod.CM.blockPeriod Z₀ Z₁).matrix *ᵥ x) (Sum.inl i) =
      ((C 0).complex (HeckeCycles.GeometricSource.CM.graphInAmbient K (C 0) Z₀ (fun j => x (Sum.inl j)))).1 i
    rw [hg]
    simp [BlockPeriod.CM.blockPeriod, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks]
  · change ((BlockPeriod.CM.blockPeriod Z₀ Z₁).matrix *ᵥ x) (Sum.inr i) =
      ((C 1).complex (HeckeCycles.GeometricSource.CM.graphInAmbient K (C 1) Z₁ (fun j => x (Sum.inr j)))).1 i
    rw [hg]
    simp [BlockPeriod.CM.blockPeriod, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks]
  · change x (Sum.inl i) =
      ((C 0).complex (HeckeCycles.GeometricSource.CM.graphInAmbient K (C 0) Z₀ (fun j => x (Sum.inl j)))).2 i
    rw [hg]
  · change x (Sum.inr i) =
      ((C 1).complex (HeckeCycles.GeometricSource.CM.graphInAmbient K (C 1) Z₁ (fun j => x (Sum.inr j)))).2 i
    rw [hg]

/-- Applying the actual rational transition to a total period graph is the
same as expressing its multiplicity-basis image in the original coordinates. -/
theorem total_transition_graph
    (C D : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (b : Module.Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K))
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (PeriodTotal.CM.TotalPositions K places)) (x : PeriodTotal.CM.TotalPositions K places → ℂ) :
    (PeriodTotal.CM.totalBasisMatrix K C D b).map (algebraMap ℚ ℂ) *ᵥ Sum.elim (Z.matrix *ᵥ x) x =
      ComplexTransition.CM.totalComplexCoordinates K C (ComplexTransition.CM.complexTensorBasisChange K b (totalGraphInAmbient K D Z x)) := by
  rw [← total_graph_coordinates K D Z x]
  exact ComplexTransition.CM.total_basis_matrix_realizes_complex K C D b (totalGraphInAmbient K D Z x)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TotalPeriodGraphs.CM
