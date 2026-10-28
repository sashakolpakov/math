import OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.OperatorSiegelData

/-! # Siegel Tensor Weights -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.SiegelTensorWeights.Construction

noncomputable section

/-! The diagonal part of the concrete ambient Siegel region acts
diagonally on ordinary integral bracket coordinates. -/

open scoped Classical OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.UnitAction.Construction.BracketAction

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

def ambientSiegelTensorWeight {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (a : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) (p : Fin m × Fin m × Fin m) : ℝ :=
  let M := (VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom b a⁻¹).val
  M p.2.2 p.2.2 * (M p.1 p.1)⁻¹ * (M p.2.1 p.2.1)⁻¹

theorem ambientSiegelTensorWeight_action {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (a : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) (ha : a ∈ OperatorSiegelData.Construction.ambientSiegelDiagonal b)
    (B : L →L[ℝ] L →L[ℝ] L) (p : Fin m × Fin m × Fin m) :
    Bilinear.DiagonalCoordinates.Construction.continuousBilinearCoordinates b.toBasis (a⁻¹ • B) p =
      ambientSiegelTensorWeight b a p * Bilinear.DiagonalCoordinates.Construction.continuousBilinearCoordinates b.toBasis B p := by
  obtain ⟨d, hd, _, hdiag⟩ := ha
  rcases p with ⟨i, j, l⟩
  have he (r : Fin m) : (a.val⁻¹).val (b r) = d r • b r :=
    VolumeMatrixOperatorLift.Construction.continuousEndMatrix_diagonal_basis b.toBasis (a.val⁻¹).val d hdiag r
  have hw : ambientSiegelTensorWeight b a (i, j, l) = d l * (d i)⁻¹ * (d j)⁻¹ := by
    simp only [ambientSiegelTensorWeight, hdiag, Matrix.diagonal_apply_eq]
  rw [hw]
  exact Bilinear.DiagonalCoordinates.Construction.continuousBilinearCoordinates_diagonal_action b.toBasis a.val⁻¹ d
    (fun r => (hd r).ne') he B i j l

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.SiegelTensorWeights.Construction
