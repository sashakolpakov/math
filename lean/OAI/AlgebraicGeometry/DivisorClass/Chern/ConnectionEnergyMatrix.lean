import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Connection Energy Matrix -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectionEnergyMatrix

noncomputable section

/-! Exact real Hilbert matrix expansion of a first-order connection energy. -/

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

def connectionPrincipalMatrix (A S : G →L[ℝ] G) : G →L[ℝ] G := S.adjoint.comp (A.comp S)

def connectionValueGradientMatrix (A S : G →L[ℝ] G) (K : F →L[ℝ] G) : F →L[ℝ] G :=
  S.adjoint.comp (A.comp K)

def connectionGradientValueMatrix (A S : G →L[ℝ] G) (K : F →L[ℝ] G) : G →L[ℝ] F :=
  K.adjoint.comp (A.comp S)

def connectionValueMatrix (A : G →L[ℝ] G) (K : F →L[ℝ] G) : F →L[ℝ] F := K.adjoint.comp (A.comp K)

theorem connectionEnergy_matrix_expansion (A S : G →L[ℝ] G) (K : F →L[ℝ] G)
    (v w : G) (a c : F) :
    inner ℝ (A (S v + K a)) (S w + K c) =
      inner ℝ (connectionPrincipalMatrix A S v) w +
      inner ℝ (connectionValueGradientMatrix A S K a) w +
      inner ℝ (connectionGradientValueMatrix A S K v) c +
      inner ℝ (connectionValueMatrix A K a) c := by
  simp only [map_add, inner_add_left, inner_add_right, connectionPrincipalMatrix,
    connectionValueGradientMatrix, connectionGradientValueMatrix, connectionValueMatrix,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
  ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectionEnergyMatrix
