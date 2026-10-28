import OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectionEnergyMatrix
import OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.ScaledCoefficient
import OAI.Analysis.HodgeTheory.Decomposition.ComplexOperatorLift

/-! # Connection Matrix Complex -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectionMatrixComplex

noncomputable section

/-! The exact connection energy blocks preserve complex scalar multiplication, including their real Hilbert adjoints. -/

open OAI.Analysis.HodgeTheory.Decomposition.ComplexOperatorLift.Constructions

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [InnerProductSpace ℝ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [InnerProductSpace ℝ G]
  [IsScalarTower ℝ ℂ G] [CompleteSpace G]

omit [IsScalarTower ℝ ℂ F] [CompleteSpace F] in
theorem connectionValueGradientMatrix_complex_smul (A S : G →L[ℝ] G) (K : F →L[ℝ] G)
    (hA : ∀ (r : ℂ) (v : G), A (r • v) = r • A v)
    (hS : ∀ (r : ℂ) (v : G), S (r • v) = r • S v)
    (hK : ∀ (r : ℂ) (v : F), K (r • v) = r • K v) (r : ℂ) (v : F) :
    ConnectionEnergyMatrix.connectionValueGradientMatrix A S K (r • v) = r • ConnectionEnergyMatrix.connectionValueGradientMatrix A S K v := by
  change S.adjoint (A (K (r • v))) = r • S.adjoint (A (K v))
  rw [hK, hA, Analysis.HodgeTheory.Decomposition.ComplexOperatorLift.Constructions.real_adjoint_complex_smul S hS]

theorem connectionGradientValueMatrix_complex_smul (A S : G →L[ℝ] G) (K : F →L[ℝ] G)
    (hA : ∀ (r : ℂ) (v : G), A (r • v) = r • A v)
    (hS : ∀ (r : ℂ) (v : G), S (r • v) = r • S v)
    (hK : ∀ (r : ℂ) (v : F), K (r • v) = r • K v) (r : ℂ) (v : G) :
    ConnectionEnergyMatrix.connectionGradientValueMatrix A S K (r • v) = r • ConnectionEnergyMatrix.connectionGradientValueMatrix A S K v := by
  change K.adjoint (A (S (r • v))) = r • K.adjoint (A (S v))
  rw [hS, hA, Analysis.HodgeTheory.Decomposition.ComplexOperatorLift.Constructions.real_adjoint_complex_smul K hK]

theorem connectionValueMatrix_complex_smul (A : G →L[ℝ] G) (K : F →L[ℝ] G)
    (hA : ∀ (r : ℂ) (v : G), A (r • v) = r • A v)
    (hK : ∀ (r : ℂ) (v : F), K (r • v) = r • K v) (r : ℂ) (v : F) :
    ConnectionEnergyMatrix.connectionValueMatrix A K (r • v) = r • ConnectionEnergyMatrix.connectionValueMatrix A K v := by
  change K.adjoint (A (K (r • v))) = r • K.adjoint (A (K v))
  rw [hK, hA, Analysis.HodgeTheory.Decomposition.ComplexOperatorLift.Constructions.real_adjoint_complex_smul K hK]

theorem complexScaleCoefficient_complex_smul (c : ℂ) (A : F →L[ℝ] F)
    (hA : ∀ (r : ℂ) (v : F), A (r • v) = r • A v) (r : ℂ) (v : F) :
    Complex.ScaledCoefficient.complexScaleCoefficient c A (r • v) = r • Complex.ScaledCoefficient.complexScaleCoefficient c A v := by
  let S := (c • ContinuousLinearMap.id ℂ F).restrictScalars ℝ
  have hS (d : ℂ) (w : F) : S (d • w) = d • S w := smul_comm c d w
  change S.adjoint (A (S (r • v))) = r • S.adjoint (A (S v))
  rw [hS, hA, Analysis.HodgeTheory.Decomposition.ComplexOperatorLift.Constructions.real_adjoint_complex_smul S hS]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectionMatrixComplex
